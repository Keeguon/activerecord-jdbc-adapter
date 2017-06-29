# NOTE: file contains code adapted from **sqlserver** adapter, license follows
=begin
Copyright (c) 2008-2015

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
=end

ArJdbc.load_java_part :MSSQL

require 'strscan'

module ArJdbc
  module MSSQL

    require 'arjdbc/mssql/utils'
    require 'arjdbc/mssql/limit_helpers'
    require 'arjdbc/mssql/lock_methods'
    require 'arjdbc/mssql/column'
    require 'arjdbc/mssql/explain_support'
    require 'arjdbc/mssql/schema_cache'
    require 'arjdbc/mssql/types' if AR42

    include LimitHelpers
    include Utils
    include ExplainSupport

    # @private
    def self.extended(adapter)
      initialize!

      version = adapter.config[:sqlserver_version] ||= adapter.sqlserver_version
      adapter.send(:setup_limit_offset!, version)
    end

    # @private
    @@_initialized = nil

    # @private
    def self.initialize!
      return if @@_initialized; @@_initialized = true

      require 'arjdbc/util/serialized_attributes'
      Util::SerializedAttributes.setup /image/i, 'after_save_with_mssql_lob'
    end

    # @private
    @@update_lob_values = true

    # Updating records with LOB values (binary/text columns) in a separate
    # statement can be disabled using :
    #
    #   ArJdbc::MSSQL.update_lob_values = false
    #
    # @note This only applies when prepared statements are not used.
    def self.update_lob_values?; @@update_lob_values; end
    # @see #update_lob_values?
    def self.update_lob_values=(update); @@update_lob_values = update; end

    # @private
    @@cs_equality_operator = 'COLLATE Latin1_General_CS_AS_WS'

    # Operator for sorting strings in SQLServer, setup as :
    #
    #  ArJdbc::MSSQL.cs_equality_operator = 'COLLATE Latin1_General_CS_AS_WS'
    #
    def self.cs_equality_operator; @@cs_equality_operator; end
    # @see #cs_equality_operator
    def self.cs_equality_operator=(operator); @@cs_equality_operator = operator; end

    # @see #quote
    # @private
    BLOB_VALUE_MARKER = "''"

    # @see #update_lob_values?
    # @see ArJdbc::Util::SerializedAttributes#update_lob_columns
    def update_lob_value?(value, column = nil)
      MSSQL.update_lob_values? && ! prepared_statements? # && value
    end

    # @see ActiveRecord::ConnectionAdapters::JdbcAdapter#jdbc_connection_class
    def self.jdbc_connection_class
      ::ActiveRecord::ConnectionAdapters::MSSQLJdbcConnection
    end

    # @see ActiveRecord::ConnectionAdapters::JdbcAdapter#jdbc_column_class
    def jdbc_column_class; ::ActiveRecord::ConnectionAdapters::MSSQLColumn end

    # @see ActiveRecord::ConnectionAdapters::Jdbc::ArelSupport
    def self.arel_visitor_type(config)
      require 'arel/visitors/sql_server'
      ( config && config[:sqlserver_version].to_s == '2000' ) ?
        ::Arel::Visitors::SQLServer2000 : ::Arel::Visitors::SQLServer
    end

    def self.arel_visitor_type(config)
      require 'arel/visitors/sql_server'; ::Arel::Visitors::SQLServerNG
    end if AR42

    # @deprecated no longer used
    # @see ActiveRecord::ConnectionAdapters::JdbcAdapter#arel2_visitors
    def self.arel2_visitors(config)
      visitor = arel_visitor_type(config)
      { 'mssql' => visitor, 'jdbcmssql' => visitor, 'sqlserver' => visitor }
    end

    def configure_connection
      use_database # config[:database]
    end

    def sqlserver_version
      @sqlserver_version ||= begin
        config_version = config[:sqlserver_version]
        config_version ? config_version.to_s :
          select_value("SELECT @@version")[/(Microsoft SQL Server\s+|Microsoft SQL Azure.+\n.+)(\d{4})/, 2]
      end
    end

    NATIVE_DATABASE_TYPES = {
      :primary_key => 'int NOT NULL IDENTITY(1,1) PRIMARY KEY',
      :integer   =>  { :name => 'int', }, # :limit => 4
      :boolean   =>  { :name => 'bit' },
      :decimal   =>  { :name => 'decimal' },
      :float     =>  { :name => 'float' },
      :bigint    =>  { :name => 'bigint' },
      :real      =>  { :name => 'real' },
      :date      =>  { :name => 'date' },
      :time      =>  { :name => 'time' },
      :datetime  =>  { :name => 'datetime' },
      :timestamp =>  { :name => 'datetime' },

      :string    =>  { :name => 'nvarchar', :limit => 4000 },
      #:varchar    =>  { :name => 'varchar' }, # limit: 8000
      :text      =>  { :name => 'nvarchar(max)' },
      :text_basic =>  { :name => 'text' },
      #:ntext      =>  { :name => 'ntext' },
      :char      =>  { :name => 'char' },
      #:nchar     =>  { :name => 'nchar' },
      :binary    =>  { :name => 'image' }, # NOTE: :name => 'varbinary(max)'
      :binary_basic => { :name => 'binary' },
      :uuid      =>  { :name => 'uniqueidentifier' },
      :money     =>  { :name => 'money' },
      #:smallmoney => { :name => 'smallmoney' },
    }

    def native_database_types
      # NOTE: due compatibility we're using the generic type resolution
      # ... NATIVE_DATABASE_TYPES won't be used at all on SQLServer 2K
      sqlserver_2000? ? super : super.merge(NATIVE_DATABASE_TYPES)
    end

    def modify_types(types)
      if sqlserver_2000?
        types[:primary_key] = NATIVE_DATABASE_TYPES[:primary_key]
        types[:string] = NATIVE_DATABASE_TYPES[:string]
        types[:boolean] = NATIVE_DATABASE_TYPES[:boolean]
        types[:text] = { :name => "ntext" }
        types[:integer][:limit] = nil
        types[:binary] = { :name => "image" }
      else
        # ~ private types for better "native" adapter compatibility
        types[:varchar_max]   =  { :name => 'varchar(max)' }
        types[:nvarchar_max]  =  { :name => 'nvarchar(max)' }
        types[:varbinary_max] =  { :name => 'varbinary(max)' }
      end
      types[:string][:limit] = 255 unless AR40 # backwards compatibility
      types
    end

    # @private these cannot specify a limit
    NO_LIMIT_TYPES = %w( text binary boolean date datetime )

    def type_to_sql(type, limit = nil, precision = nil, scale = nil)
      type_s = type.to_s
      # MSSQL's NVARCHAR(n | max) column supports either a number between 1 and
      # 4000, or the word "MAX", which corresponds to 2**30-1 UCS-2 characters.
      #
      # It does not accept NVARCHAR(1073741823) here, so we have to change it
      # to NVARCHAR(MAX), even though they are logically equivalent.
      #
      # MSSQL Server 2000 is skipped here because I don't know how it will behave.
      #
      # See: http://msdn.microsoft.com/en-us/library/ms186939.aspx
      if type_s == 'string' && limit == 1073741823 && ! sqlserver_2000?
        'NVARCHAR(MAX)'
      elsif NO_LIMIT_TYPES.include?(type_s)
        super(type)
      elsif type_s == 'integer' || type_s == 'int'
        if limit.nil? || limit == 4
          'int'
        elsif limit == 2
          'smallint'
        elsif limit == 1
          'tinyint'
        else
          'bigint'
        end
      elsif type_s == 'uniqueidentifier'
        type_s
      else
        super
      end
    end

    def column_definitions(table_name)
      db_name = unqualify_db_name(table_name)
      db_name_with_period = "#{db_name}." if db_name
      table_schema = unqualify_table_schema(table_name)
      table_name = unqualify_table_name(table_name)
      sql = %{
        SELECT DISTINCT
        #{lowercase_schema_reflection_sql('columns.TABLE_NAME')} AS table_name,
        #{lowercase_schema_reflection_sql('columns.COLUMN_NAME')} AS name,
        columns.DATA_TYPE AS type,
        columns.COLUMN_DEFAULT AS default_value,
        columns.NUMERIC_SCALE AS numeric_scale,
        columns.NUMERIC_PRECISION AS numeric_precision,
        columns.ordinal_position,
        CASE
          WHEN columns.DATA_TYPE IN ('nchar','nvarchar') THEN columns.CHARACTER_MAXIMUM_LENGTH
          ELSE COL_LENGTH('#{db_name_with_period}'+columns.TABLE_SCHEMA+'.'+columns.TABLE_NAME, columns.COLUMN_NAME)
        END AS [length],
        CASE
          WHEN columns.IS_NULLABLE = 'YES' THEN 1
          ELSE NULL
        END AS [is_nullable],
        CASE
          WHEN KCU.COLUMN_NAME IS NOT NULL AND TC.CONSTRAINT_TYPE = N'PRIMARY KEY' THEN 1
          ELSE NULL
        END AS [is_primary],
        c.is_identity AS [is_identity]
        FROM #{db_name_with_period}INFORMATION_SCHEMA.COLUMNS columns
        LEFT OUTER JOIN #{db_name_with_period}INFORMATION_SCHEMA.TABLE_CONSTRAINTS AS TC
          ON TC.TABLE_NAME = columns.TABLE_NAME
          AND TC.CONSTRAINT_TYPE = N'PRIMARY KEY'
        LEFT OUTER JOIN #{db_name_with_period}INFORMATION_SCHEMA.KEY_COLUMN_USAGE AS KCU
          ON KCU.COLUMN_NAME = columns.COLUMN_NAME
          AND KCU.CONSTRAINT_NAME = TC.CONSTRAINT_NAME
          AND KCU.CONSTRAINT_CATALOG = TC.CONSTRAINT_CATALOG
          AND KCU.CONSTRAINT_SCHEMA = TC.CONSTRAINT_SCHEMA
        INNER JOIN #{db_name}.sys.schemas AS s
          ON s.name = columns.TABLE_SCHEMA
          AND s.schema_id = s.schema_id
        INNER JOIN #{db_name}.sys.objects AS o
          ON s.schema_id = o.schema_id
          AND o.is_ms_shipped = 0
          AND o.type IN ('U', 'V')
          AND o.name = columns.TABLE_NAME
        INNER JOIN #{db_name}.sys.columns AS c
          ON o.object_id = c.object_id
          AND c.name = columns.COLUMN_NAME
        WHERE columns.TABLE_NAME = @0
          AND columns.TABLE_SCHEMA = #{table_schema.blank? ? "schema_name()" : "@1"}
        ORDER BY columns.ordinal_position
      }.gsub(/[ \t\r\n]+/,' ')
      binds = [['table_name', table_name]]
      binds << ['table_schema',table_schema] unless table_schema.blank?
      results = exec_query(sql, 'SCHEMA', binds)
      results.collect do |ci|
        ci = ci.symbolize_keys
        ci[:type] = case ci[:type]
                     when /^bit|image|text|ntext|datetime$/
                       ci[:type]
                     when /^numeric|decimal$/i
                       "#{ci[:type]}(#{ci[:numeric_precision]},#{ci[:numeric_scale]})"
                     when /^float|real$/i
                       "#{ci[:type]}(#{ci[:numeric_precision]})"
                     when /^char|nchar|varchar|nvarchar|varbinary|bigint|int|smallint$/
                       ci[:length].to_i == -1 ? "#{ci[:type]}(max)" : "#{ci[:type]}(#{ci[:length]})"
                     else
                       ci[:type]
                     end
        if ci[:default_value].nil? && schema_cache.view_names.include?(table_name)
          real_table_name = table_name_or_views_table_name(table_name)
          real_column_name = views_real_column_name(table_name,ci[:name])
          col_default_sql = "SELECT c.COLUMN_DEFAULT FROM #{db_name_with_period}INFORMATION_SCHEMA.COLUMNS c WHERE c.TABLE_NAME = '#{real_table_name}' AND c.COLUMN_NAME = '#{real_column_name}'"
          ci[:default_value] = select_value col_default_sql, 'SCHEMA'
        end
        ci[:default_value] = case ci[:default_value]
                             when nil, '(null)', '(NULL)'
                               nil
                             when /\A\((\w+\(\))\)\Z/
                               ci[:default_function] = $1
                               nil
                             else
                               match_data = ci[:default_value].match(/\A\(+N?'?(.*?)'?\)+\Z/m)
                               match_data ? match_data[1] : nil
                             end
        ci[:null] = ci[:is_nullable].to_i == 1 ; ci.delete(:is_nullable)
        ci[:is_primary] = ci[:is_primary].to_i == 1
        ci[:is_identity] = ci[:is_identity].to_i == 1 unless [TrueClass, FalseClass].include?(ci[:is_identity].class)
        ci
      end
    end

    def lowercase_schema_reflection_sql(node)
      lowercase_schema_reflection ? "LOWER(#{node})" : node
    end

    # === SQLServer Specific (View Reflection) ====================== #

    def view_table_name(table_name)
      view_info = schema_cache.view_information(table_name)
      view_info ? get_table_name(view_info['VIEW_DEFINITION']) : table_name
    end

    def view_information(table_name)
      table_name = Utils.unqualify_table_name(table_name)
      view_info = select_one "SELECT * FROM INFORMATION_SCHEMA.VIEWS WHERE TABLE_NAME = '#{table_name}'", 'SCHEMA'
      if view_info
        view_info = view_info.with_indifferent_access
        if view_info[:VIEW_DEFINITION].blank? || view_info[:VIEW_DEFINITION].length == 4000
          view_info[:VIEW_DEFINITION] = begin
                                          select_values("EXEC sp_helptext #{quote_table_name(table_name)}", 'SCHEMA').join
                                        rescue
                                          warn "No view definition found, possible permissions problem.\nPlease run GRANT VIEW DEFINITION TO your_user;"
                                          nil
                                        end
        end
      end
      view_info
    end

    def table_name_or_views_table_name(table_name)
      unquoted_table_name = Utils.unqualify_table_name(table_name)
      schema_cache.view_names.include?(unquoted_table_name) ? view_table_name(unquoted_table_name) : unquoted_table_name
    end

    def views_real_column_name(table_name,column_name)
      view_definition = schema_cache.view_information(table_name)[:VIEW_DEFINITION]
      match_data = view_definition.match(/([\w-]*)\s+as\s+#{column_name}/im)
      match_data ? match_data[1] : column_name
    end

    # @override
    def quote(value, column = nil)
      return value.quoted_id if value.respond_to?(:quoted_id)
      return value if sql_literal?(value)

      case value
      # SQL Server 2000 doesn't let you insert an integer into a NVARCHAR
      when String, ActiveSupport::Multibyte::Chars, Integer
        value = value.to_s
        column_type = column && column.type
        if column_type == :binary
          if update_lob_value?(value, column)
            BLOB_VALUE_MARKER
          else
            "'#{quote_string(column.class.string_to_binary(value))}'" # ' (for ruby-mode)
          end
        elsif column_type == :integer
          value.to_i.to_s
        elsif column_type == :float
          value.to_f.to_s
        elsif ! column.respond_to?(:is_utf8?) || column.is_utf8?
          "N'#{quote_string(value)}'" # ' (for ruby-mode)
        else
          super
        end
      when Date, Time
        if column && column.type == :time
          "'#{quoted_time(value)}'"
        else
          "'#{quoted_date(value)}'"
        end
      when TrueClass  then '1'
      when FalseClass then '0'
      else super
      end
    end

    # @override
    def quoted_date(value)
      if value.respond_to?(:usec)
        "#{super}.#{sprintf("%03d", value.usec / 1000)}"
      else
        super
      end
    end

    # @private
    def quoted_time(value)
      if value.acts_like?(:time)
        tz_value = get_time(value)
        usec = value.respond_to?(:usec) ? ( value.usec / 1000 ) : 0
        sprintf("%02d:%02d:%02d.%03d", tz_value.hour, tz_value.min, tz_value.sec, usec)
      else
        quoted_date(value)
      end
    end

    # @deprecated no longer used
    # @private
    def quoted_datetime(value)
      quoted_date(value)
    end

    # @deprecated no longer used
    # @private
    def quoted_full_iso8601(value)
      if value.acts_like?(:time)
        value.is_a?(Date) ?
          get_time(value).to_time.xmlschema.to(18) :
            get_time(value).iso8601(7).to(22)
      else
        quoted_date(value)
      end
    end

    def quote_table_name(name)
      quote_column_name(name)
    end

    def quote_column_name(name)
      name = name.to_s.split('.')
      name.map! { |n| quote_name_part(n) } # "[#{name}]"
      name.join('.')
    end

    def quote_database_name(name)
      quote_name_part(name.to_s)
    end

    # Does not quote function default values for UUID columns
    def quote_default_value(value, column)
      if column.type == :uuid && value =~ /\(\)/
        value
      else
        quote(value)
      end
    end

    ADAPTER_NAME = 'MSSQL'.freeze

    def adapter_name
      ADAPTER_NAME
    end

    def change_order_direction(order)
      asc, desc = /\bASC\b/i, /\bDESC\b/i
      order.split(",").collect do |fragment|
        case fragment
        when desc  then fragment.gsub(desc, "ASC")
        when asc   then fragment.gsub(asc, "DESC")
        else "#{fragment.split(',').join(' DESC,')} DESC"
        end
      end.join(",")
    end

    # @override
    def supports_ddl_transactions?; true end

    # @override
    def supports_views?; true end

    def tables(schema = current_schema)
      @connection.tables(nil, schema)
    end

    # NOTE: Dynamic Name Resolution - SQL Server 2000 vs. 2005
    #
    # A query such as "select * from table1" in SQL Server 2000 goes through
    # a set of steps to resolve and validate the object references before
    # execution.
    # The search first looks at the identity of the connection executing
    # the query.
    #
    # However SQL Server 2005 provides a mechanism to allow finer control over
    # name resolution to the administrators. By manipulating the value of the
    # default_schema_name columns in the sys.database_principals.
    #
    # http://blogs.msdn.com/b/mssqlisv/archive/2007/03/23/upgrading-to-sql-server-2005-and-default-schema-setting.aspx

    # Returns the default schema (to be used for table resolution) used for the {#current_user}.
    def default_schema
      return current_user if sqlserver_2000?
      @default_schema ||=
        @connection.execute_query_raw(
          "SELECT default_schema_name FROM sys.database_principals WHERE name = CURRENT_USER"
        ).first['default_schema_name']
    end
    alias_method :current_schema, :default_schema

    # Allows for changing of the default schema (to be used during unqualified
    # table name resolution).
    # @note This is not supported on SQL Server 2000 !
    def default_schema=(default_schema) # :nodoc:
      raise "changing DEFAULT_SCHEMA only supported on SQLServer 2005+" if sqlserver_2000?
      execute("ALTER #{current_user} WITH DEFAULT_SCHEMA=#{default_schema}")
      @default_schema = nil if defined?(@default_schema)
    end
    alias_method :current_schema=, :default_schema=

    # `SELECT CURRENT_USER`
    def current_user
      @current_user ||= @connection.execute_query_raw("SELECT CURRENT_USER").first['']
    end

    def charset
      select_value "SELECT SERVERPROPERTY('SqlCharSetName')"
    end

    def collation
      select_value "SELECT SERVERPROPERTY('Collation')"
    end

    def current_database
      select_value 'SELECT DB_NAME()'
    end

    def use_database(database = nil)
      database ||= config[:database]
      execute "USE #{quote_database_name(database)}" unless database.blank?
    end

    # @private
    def recreate_database(name, options = {})
      drop_database(name)
      create_database(name, options)
    end

    # @private
    def recreate_database!(database = nil)
      current_db = current_database
      database ||= current_db
      use_database('master') if this_db = ( database.to_s == current_db )
      drop_database(database)
      create_database(database)
    ensure
      use_database(current_db) if this_db
    end

    def drop_database(name)
      current_db = current_database
      use_database('master') if current_db.to_s == name
      execute "DROP DATABASE #{quote_database_name(name)}"
    end

    def create_database(name, options = {})
      execute "CREATE DATABASE #{quote_database_name(name)}"
    end

    def database_exists?(name)
      select_value "SELECT name FROM sys.databases WHERE name = '#{name}'"
    end

    # @override
    def rename_table(table_name, new_table_name)
      clear_cached_table(table_name)
      execute "EXEC sp_rename '#{table_name}', '#{new_table_name}'"
    end

    # Adds a new column to the named table.
    # @override
    def add_column(table_name, column_name, type, options = {})
      clear_cached_table(table_name)
      add_column_sql = "ALTER TABLE #{quote_table_name(table_name)} ADD #{quote_column_name(column_name)} #{type_to_sql(type, options[:limit], options[:precision], options[:scale])}"
      add_column_options!(add_column_sql, options)
      # TODO: Add support to mimic date columns, using constraints to mark them as such in the database
      # add_column_sql << " CONSTRAINT ck__#{table_name}__#{column_name}__date_only CHECK ( CONVERT(CHAR(12), #{quote_column_name(column_name)}, 14)='00:00:00:000' )" if type == :date
      execute(add_column_sql)
    end

    # @override
    def rename_column(table_name, column_name, new_column_name)
      clear_cached_table(table_name)
      execute "EXEC sp_rename '#{table_name}.#{column_name}', '#{new_column_name}', 'COLUMN'"
    end

    # SELECT DISTINCT clause for a given set of columns and a given ORDER BY clause.
    # MSSQL requires the ORDER BY columns in the select list for distinct queries.
    def distinct(columns, order_by)
      "DISTINCT #{columns_for_distinct(columns, order_by)}"
    end

    def columns_for_distinct(columns, orders)
      return columns if orders.blank?

      # construct a clean list of column names from the ORDER BY clause,
      # removing any ASC/DESC modifiers
      order_columns = [ orders ]; order_columns.flatten! # AR 3.x vs 4.x
      order_columns.map! do |column|
        column = column.to_sql unless column.is_a?(String) # handle AREL node
        column.split(',').collect!{ |s| s.split.first }
      end.flatten!
      order_columns.reject!(&:blank?)
      order_columns = order_columns.zip(0...order_columns.size).to_a
      order_columns = order_columns.map{ |s, i| "#{s}" }

      columns = [ columns ]; columns.flatten!
      columns.push( *order_columns ).join(', ')
      # return a DISTINCT clause that's distinct on the columns we want but
      # includes all the required columns for the ORDER BY to work properly
    end

    # @override
    def change_column(table_name, column_name, type, options = {})
      column = columns(table_name).find { |c| c.name.to_s == column_name.to_s }

      indexes = EMPTY_ARRAY
      if options_include_default?(options) || (column && column.type != type.to_sym)
        remove_default_constraint(table_name, column_name)
        indexes = indexes(table_name).select{ |index| index.columns.include?(column_name.to_s) }
        remove_indexes(table_name, column_name)
      end

      if ! options[:null].nil? && options[:null] == false && ! options[:default].nil?
        execute "UPDATE #{quote_table_name(table_name)} SET #{quote_column_name(column_name)}=#{quote_default_value(options[:default], column)} WHERE #{quote_column_name(column_name)} IS NULL"
        clear_cached_table(table_name)
      end
      change_column_type(table_name, column_name, type, options)
      change_column_default(table_name, column_name, options[:default]) if options_include_default?(options)

      indexes.each do |index| # add any removed indexes back
        index_columns = index.columns.map { |c| quote_column_name(c) }.join(', ')
        execute "CREATE INDEX #{quote_table_name(index.name)} ON #{quote_table_name(table_name)} (#{index_columns})"
      end
    end

    def change_column_type(table_name, column_name, type, options = {})
      sql = "ALTER TABLE #{quote_table_name(table_name)} ALTER COLUMN #{quote_column_name(column_name)} #{type_to_sql(type, options[:limit], options[:precision], options[:scale])}"
      sql << (options[:null] ? " NULL" : " NOT NULL") if options.has_key?(:null)
      result = execute(sql)
      clear_cached_table(table_name)
      result
    end

    def change_column_default(table_name, column_name, default)
      remove_default_constraint(table_name, column_name)
      unless default.nil?
        column = columns(table_name).find { |c| c.name.to_s == column_name.to_s }
        result = execute "ALTER TABLE #{quote_table_name(table_name)} ADD CONSTRAINT DF_#{table_name}_#{column_name} DEFAULT #{quote_default_value(default, column)} FOR #{quote_column_name(column_name)}"
        clear_cached_table(table_name)
        result
      end
    end

    def remove_columns(table_name, *column_names)
      raise ArgumentError.new("You must specify at least one column name. Example: remove_column(:people, :first_name)") if column_names.empty?
      # remove_columns(:posts, :foo, :bar) old syntax : remove_columns(:posts, [:foo, :bar])
      clear_cached_table(table_name)

      column_names = column_names.flatten
      return do_remove_column(table_name, column_names.first) if column_names.size == 1
      column_names.each { |column_name| do_remove_column(table_name, column_name) }
    end

    def do_remove_column(table_name, column_name)
      remove_check_constraints(table_name, column_name)
      remove_default_constraint(table_name, column_name)
      remove_indexes(table_name, column_name) unless sqlserver_2000?
      execute "ALTER TABLE #{quote_table_name(table_name)} DROP COLUMN #{quote_column_name(column_name)}"
    end
    private :do_remove_column

    if ActiveRecord::VERSION::MAJOR >= 4

    # @override
    def remove_column(table_name, column_name, type = nil, options = {})
      remove_columns(table_name, column_name)
    end

    else

    def remove_column(table_name, *column_names); remove_columns(table_name, *column_names) end

    end

    def remove_default_constraint(table_name, column_name)
      clear_cached_table(table_name)
      if sqlserver_2000?
        # NOTE: since SQLServer 2005 these are provided as sys.sysobjects etc.
        # but only due backwards-compatibility views and should be avoided ...
        defaults = select_values "SELECT d.name" <<
          " FROM sysobjects d, syscolumns c, sysobjects t" <<
          " WHERE c.cdefault = d.id AND c.name = '#{column_name}'" <<
          " AND t.name = '#{table_name}' AND c.id = t.id"
      else
        defaults = select_values "SELECT d.name FROM sys.tables t" <<
          " JOIN sys.default_constraints d ON d.parent_object_id = t.object_id" <<
          " JOIN sys.columns c ON c.object_id = t.object_id AND c.column_id = d.parent_column_id" <<
          " WHERE t.name = '#{table_name}' AND c.name = '#{column_name}'"
      end
      defaults.each do |def_name|
        execute "ALTER TABLE #{table_name} DROP CONSTRAINT #{def_name}"
      end
    end

    def remove_check_constraints(table_name, column_name)
      clear_cached_table(table_name)
      constraints = select_values "SELECT constraint_name" <<
        " FROM INFORMATION_SCHEMA.CONSTRAINT_COLUMN_USAGE" <<
        " WHERE table_name = '#{table_name}' AND column_name = '#{column_name}'"
      constraints.each do |constraint_name|
        execute "ALTER TABLE #{table_name} DROP CONSTRAINT #{constraint_name}"
      end
    end

    def remove_indexes(table_name, column_name)
      indexes = self.indexes(table_name)
      indexes.select{ |index| index.columns.include?(column_name.to_s) }.each do |index|
        remove_index(table_name, { :name => index.name })
      end
    end

    def remove_index(table_name, options = {})
      execute "DROP INDEX #{quote_table_name(table_name)}.#{index_name(table_name, options)}"
    end

    # @private
    SKIP_COLUMNS_TABLE_NAMES_RE = /^information_schema\./i

    # @private
    EMPTY_ARRAY = [].freeze

    def columns(table_name, name = nil, default = EMPTY_ARRAY)
      return [] if table_name.blank?
      column_definitions(table_name).collect do |ci|
        sqlserver_options = ci.except(:name,:default_value,:type,:null).merge(:database_year=>database_year)
        jdbc_column_class.new ci[:name], ci[:default_value], ci[:type], ci[:null], sqlserver_options
      end
    end

    def clear_cached_table(table_name)
      ( @table_columns ||= {} ).delete(table_name.to_s)
    end

    def reset_column_information
      @table_columns = nil if defined? @table_columns
    end

    # Turns IDENTITY_INSERT ON for table during execution of the block
    # N.B. This sets the state of IDENTITY_INSERT to OFF after the
    # block has been executed without regard to its previous state
    def with_identity_insert_enabled(table_name)
      set_identity_insert(table_name, true)
      yield
    ensure
      set_identity_insert(table_name, false)
    end

    def set_identity_insert(table_name, enable = true)
      execute "SET IDENTITY_INSERT #{table_name} #{enable ? 'ON' : 'OFF'}"
    rescue Exception => e
      raise ActiveRecord::ActiveRecordError, "IDENTITY_INSERT could not be turned" +
            " #{enable ? 'ON' : 'OFF'} for table #{table_name} due : #{e.inspect}"
    end

    def disable_referential_integrity
      execute "EXEC sp_MSforeachtable 'ALTER TABLE ? NOCHECK CONSTRAINT ALL'"
      yield
    ensure
      execute "EXEC sp_MSforeachtable 'ALTER TABLE ? CHECK CONSTRAINT ALL'"
    end

    # @private
    # @see ArJdbc::MSSQL::LimitHelpers
    def determine_order_clause(sql)
      return $1 if sql =~ /ORDER BY (.*)$/i
      columns = self.columns(table_name = get_table_name(sql))
      primary_column = columns.find { |column| column.primary? || column.identity? }
      unless primary_column # look for an id column and return it,
        # without changing case, to cover DBs with a case-sensitive collation :
        primary_column = columns.find { |column| column.name =~ /^id$/i }
        raise "no columns for table: #{table_name}" if columns.empty?
      end
      # NOTE: if still no PK column simply get something for ORDER BY ...
      "#{quote_table_name(table_name)}.#{quote_column_name((primary_column || columns.first).name)}"
    end

    def truncate(table_name, name = nil)
      execute "TRUNCATE TABLE #{quote_table_name(table_name)}", name
    end

    # Support for executing a stored procedure.
    def exec_proc(proc_name, *variables)
      vars =
        if variables.any? && variables.first.is_a?(Hash)
          variables.first.map { |k, v| "@#{k} = #{quote(v)}" }
        else
          variables.map { |v| quote(v) }
        end.join(', ')
      sql = "EXEC #{proc_name} #{vars}".strip
      log(sql, 'Execute Procedure') do
        result = @connection.execute_query_raw(sql)
        result.map! do |row|
          row = row.is_a?(Hash) ? row.with_indifferent_access : row
          yield(row) if block_given?
          row
        end
        result
      end
    end
    alias_method :execute_procedure, :exec_proc # AR-SQLServer-Adapter naming

    # @override
    def exec_query(sql, name = 'SQL', binds = [])
      # NOTE: we allow to execute SQL as requested returning a results.
      # e.g. this allows to use SQLServer's EXEC with a result set ...
      if sql.respond_to?(:to_sql)
        sql = to_sql(sql, binds); to_sql = true
      end
      sql = repair_special_columns(sql)
      if prepared_statements?
        log(sql, name, binds) { @connection.execute_query(sql, binds) }
      else
        sql = suble_binds(sql, binds) unless to_sql # deprecated behavior
        log(sql, name) { @connection.execute_query(sql) }
      end
    end

    # @override
    def exec_query_raw(sql, name = 'SQL', binds = [], &block)
      if sql.respond_to?(:to_sql)
        sql = to_sql(sql, binds); to_sql = true
      end
      sql = repair_special_columns(sql)
      if prepared_statements?
        log(sql, name, binds) { @connection.execute_query_raw(sql, binds, &block) }
      else
        sql = suble_binds(sql, binds) unless to_sql # deprecated behavior
        log(sql, name) { @connection.execute_query_raw(sql, &block) }
      end
    end

    # @override
    def exec_insert(sql, name = 'SQL', binds = [], pk = nil, sequence_name = nil)
      if id_insert_table_name = identity_insert_table_name(sql)
        with_identity_insert_enabled(id_insert_table_name) do
          super(sql, name, binds, pk, sequence_name)
        end
      else
        super(sql, name, binds, pk, sequence_name)
      end
    end

    # @override
    def release_savepoint(name = current_savepoint_name(false))
      if @connection.jtds_driver?
        @connection.release_savepoint(name)
      else # MS invented it's "own" way
        @connection.rollback_savepoint(name)
      end
    end

    private

    def _execute(sql, name = nil)
      # Match the start of the SQL to determine appropriate behavior.
      # Be aware of multi-line SQL which might begin with 'create stored_proc'
      # and contain 'insert into ...' lines.
      # NOTE: ignoring comment blocks prior to the first statement ?!
      if self.class.insert?(sql)
        if id_insert_table_name = identity_insert_table_name(sql)
          with_identity_insert_enabled(id_insert_table_name) do
            @connection.execute_insert(sql)
          end
        else
          @connection.execute_insert(sql)
        end
      elsif self.class.select?(sql)
        @connection.execute_query_raw repair_special_columns(sql)
      else # create | exec
        @connection.execute_update(sql)
      end
    end

    def identity_insert_table_name(sql)
      table_name = get_table_name(sql)
      id_column = identity_column_name(table_name)
      if id_column && sql.strip =~ /INSERT INTO [^ ]+ ?\((.+?)\)/i
        insert_columns = $1.split(/, */).map(&method(:unquote_column_name))
        return table_name if insert_columns.include?(id_column)
      end
    end

    def identity_column_name(table_name)
      for column in columns(table_name)
        return column.name if column.identity
      end
      nil
    end

    def repair_special_columns(sql)
      qualified_table_name = get_table_name(sql, true)
      if special_columns = special_column_names(qualified_table_name)
        return sql if special_columns.empty?
        special_columns = special_columns.sort { |n1, n2| n2.size <=> n1.size }
        for column in special_columns
          sql.gsub!(/\s?\[?#{column}\]?\s?=\s?/, " [#{column}] LIKE ")
          sql.gsub!(/ORDER BY \[?#{column}([^\.\w]|$)\]?/i, '') # NOTE: a bit stupid
        end
      end
      sql
    end

    def special_column_names(qualified_table_name)
      columns = self.columns(qualified_table_name, nil, nil)
      return columns if ! columns || columns.empty?
      special = []
      columns.each { |column| special << column.name if column.special? }
      special
    end

    def sqlserver_2000?
      sqlserver_version <= '2000'
    end

  end
end

require 'arjdbc/util/quoted_cache'

module ActiveRecord::ConnectionAdapters

  class MSSQLAdapter < JdbcAdapter
    include ::ArJdbc::MSSQL
    include ::ArJdbc::Util::QuotedCache

    def initialize(*args)
      ::ArJdbc::MSSQL.initialize!

      super # configure_connection happens in super

      @schema_cache = ::ArJdbc::MSSQL::SchemaCache.new self

      setup_limit_offset!
    end

    def self.cs_equality_operator; ::ArJdbc::MSSQL.cs_equality_operator end
    def self.cs_equality_operator=(operator); ::ArJdbc::MSSQL.cs_equality_operator = operator end

  end

  class MSSQLColumn < JdbcColumn
    include ::ArJdbc::MSSQL::Column
  end

end
