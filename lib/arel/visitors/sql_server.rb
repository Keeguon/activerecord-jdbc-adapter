require 'arel/visitors/compat'

module Arel
  module Visitors
    class SQLServer < Arel::Visitors::ToSql
      private

      # SQLServer ToSql/Visitor (Overides)
      def visit_Arel_Nodes_SelectStatement o, collector
        if complex_count_sql?(o)
          visit_Arel_Nodes_SelectStatementForComplexCount o, collector
        elsif distinct_non_present_orders? o, collector
          visit_Arel_Nodes_SelectStatementDistinctNonPresentOrders o, collector
        elsif o.offset
          visit_Arel_Nodes_SelectStatementWithOffset o, collector
        else
          visit_Arel_Nodes_SelectStatementWithOutOffset o, collector
        end
      end

      def visit_Arel_Nodes_UpdateStatement o, collector
        if o.orders.any? && o.limit.nil?
          o.limit = Nodes::Limit.new(9_223_372_036_854_775_807)
        end
        super
      end

      def visit_Arel_Nodes_Offset o, collector
        "WHERE [__rnt].[__rn] > (#{visit o.expr, collector})"
      end

      def visit_Arel_Nodes_Limit o, collector
        "TOP (#{visit o.expr, collector})"
      end

      def visit_Arel_Nodes_Lock o, collector
        visit o.expr, collector
      end

      def visit_Arel_Nodes_Ordering o, collector
        if o.respond_to?(:direction)
          "#{visit o.expr, collector} #{o.ascending? ? 'ASC' : 'DESC'}"
        else
          visit o.expr, collector
        end
      end

      def visit_Arel_Nodes_Bin o, collector
        "#{visit o.expr, collector} #{::ArJdbc::MSSQL.cs_equality_operator}"
      end

      # SQLServer ToSql/Visitor (Additions)

      # This constructs a query using DENSE_RANK() and ROW_NUMBER() to allow
      # ordering a DISTINCT set of data by columns in another table that are
      # not part of what we actually want to be DISTINCT. Without this, it is
      # possible for the DISTINCT qualifier combined with TOP to return fewer
      # rows than were requested.
      def visit_Arel_Nodes_SelectStatementDistinctNonPresentOrders o, collector
        core = o.cores.first
        projections = core.projections
        groups = core.groups
        orders = o.orders.uniq

        select_frags = projections.map do |x|
          frag = projection_to_sql_remove_distinct(x, core, collector)
          # Remove the table specifier
          frag.gsub!(/^[^\.]*\./, '')
          # If there is an alias, remove everything but
          frag.gsub(/^.*\sAS\s+/i, '')
        end

        if o.offset
          select_frags << 'ROW_NUMBER() OVER (ORDER BY __order) AS __offset'
        else
          select_frags << '__order'
        end

        projection_list = projections.map { |x| projection_to_sql_remove_distinct(x, core, collector) }.join(', ')

        sql = [
          ('SELECT'),
          (visit(core.set_quantifier, collector) if core.set_quantifier && !o.offset),
          (visit(o.limit, collector) if o.limit && !o.offset),
          (select_frags.join(', ')),
          ('FROM ('),
            ('SELECT'),
            (
              [
                (projection_list),
                (', DENSE_RANK() OVER ('),
                  ("ORDER BY #{orders.map { |x| visit(x, collector) }.join(', ')}" unless orders.empty?),
                (') AS __order'),
                (', ROW_NUMBER() OVER ('),
                  ("PARTITION BY #{projection_list}" if !orders.empty?),
                  (" ORDER BY #{orders.map { |x| visit(x, collector) }.join(', ')}" unless orders.empty?),
                (') AS __joined_row_num')
              ].join('')
            ),
            (visit_Arel_Nodes_SelectStatement_SQLServer_Lock collector, space: true),
            ("WHERE #{core.wheres.map { |x| visit(x, collector) }.join ' AND ' }" unless core.wheres.empty?),
            ("GROUP BY #{groups.map { |x| visit(x, collector) }.join ', ' }" unless groups.empty?),
            (visit(core.having, collector) if core.having),
          (') AS __sq'),
          ('WHERE __joined_row_num = 1'),
          ('ORDER BY __order' unless o.offset)
        ].compact.join(' ')

        if o.offset
          sql = [
            ('SELECT'),
            (visit(core.set_quantifier, collector) if core.set_quantifier),
            (visit(o.limit, collector) if o.limit),
            ('*'),
            ('FROM (' + sql + ') AS __osq'),
            ("WHERE __offset > #{visit(o.offset.expr, collector)}"),
            ('ORDER BY __offset')
          ].join(' ')
        end

        Arel::Collector::SQLString.new(sql)
      end

      def visit_Arel_Nodes_SelectStatementWithOutOffset o, collector, windowed = false
        find_and_fix_uncorrelated_joins_in_select_statement(o)
        core = o.cores.first
        projections = core.projections
        groups = core.groups
        orders = o.orders.uniq
        if windowed
          projections = function_select_statement?(o) ? projections : projections.map { |x| projection_without_expression(x, collector) }
          groups = projections.map { |x| projection_without_expression(x, collector) } if windowed_single_distinct_select_statement?(o) && groups.empty?
          groups += orders.map { |x| Arel.sql(x.expr) } if windowed_single_distinct_select_statement?(o)
        elsif eager_limiting_select_statement? o, collector
          projections = projections.map { |x| projection_without_expression(x, collector) }
          groups = projections.map { |x| projection_without_expression(x, collector) }
          orders = orders.map do |x|
            expr = Arel.sql projection_without_expression(x.expr, collector)
            x.descending? ? Arel::Nodes::Max.new([expr]) : Arel::Nodes::Min.new([expr])
          end
        elsif top_one_everything_for_through_join?(o, collector)
          projections = projections.map { |x| projection_without_expression(x, collector) }
        end
        Arel::Collector::SQLString.new([
          ('SELECT' unless windowed),
          (visit(core.set_quantifier, collector) if core.set_quantifier && !windowed),
          (visit(o.limit, collector) if o.limit && !windowed),
          (projections.map do |x|
            v = visit(x, collector)
            v == '1' ? '1 AS [__wrp]' : v
          end.join(', ')),
          (visit_Arel_Nodes_SelectStatement_SQLServer_Lock collector, space: true),
          ("WHERE #{core.wheres.map { |x| visit(x, collector) }.join ' AND ' }" unless core.wheres.empty?),
          ("GROUP BY #{groups.map { |x| visit(x, collector) }.join ', ' }" unless groups.empty?),
          (visit(core.having, collector) if core.having),
          ("ORDER BY #{orders.map { |x| visit(x, collector) }.join(', ')}" if !orders.empty? && !windowed)
        ].compact.join(' '))
      end

      def visit_Arel_Nodes_SelectStatementWithOffset o, collector
        core = o.cores.first
        o.limit ||= Arel::Nodes::Limit.new(9_223_372_036_854_775_807)
        orders = rowtable_orders(o)
        Arel::Collector::SQLString.new([
          'SELECT',
          (visit(o.limit, collector) if o.limit && !windowed_single_distinct_select_statement?(o)),
          (rowtable_projections o, collector.map { |x| visit(x, collector) }.join(', ')),
          'FROM (',
          "SELECT #{core.set_quantifier ? 'DISTINCT DENSE_RANK()' : 'ROW_NUMBER()'} OVER (ORDER BY #{orders.map { |x| visit(x, collector) }.join(', ')}) AS [__rn],",
          visit_Arel_Nodes_SelectStatementWithOutOffset(o, collector, true),
          ') AS [__rnt]',
          (visit(o.offset, collector) if o.offset),
          'ORDER BY [__rnt].[__rn] ASC'
        ].compact.join(' '))
      end

      def visit_Arel_Nodes_SelectStatementForComplexCount o, collector
        core = o.cores.first
        o.limit.expr = Arel.sql("#{o.limit.expr} + #{o.offset ? o.offset.expr : 0}") if o.limit
        orders = rowtable_orders(o)
        Arel::Collector::SQLString.new([
          'SELECT COUNT([count]) AS [count_id]',
          'FROM (',
          'SELECT',
          (visit(o.limit, collector) if o.limit),
          "ROW_NUMBER() OVER (ORDER BY #{orders.map { |x| visit(x, collector) }.join(', ')}) AS [__rn],",
          '1 AS [count]',
          (visit_Arel_Nodes_SelectStatement_SQLServer_Lock collector, space: true),
          ("WHERE #{core.wheres.map { |x| visit(x, collector) }.join ' AND ' }" unless core.wheres.empty?),
          ("GROUP BY #{core.groups.map { |x| visit(x, collector) }.join ', ' }" unless core.groups.empty?),
          (visit(core.having, collector) if core.having),
          ("ORDER BY #{o.orders.map { |x| visit(x, collector) }.join(', ')}" unless o.orders.empty?),
          ') AS [__rnt]',
          (visit(o.offset, collector) if o.offset)
        ].compact.join(' '))
      end

      # SQLServer ToSql/Visitor (Additions)

      def visit_Arel_Nodes_SelectStatement_SQLServer_Lock collector, options = {}
        if select_statement_lock?
          collector = visit @select_statement.lock, collector
          collector << SPACE if options[:space]
        end
        collector
      end

      # SQLServer Helpers

      def projection_to_sql_remove_distinct(x, core, collector)
        frag = Arel.sql(visit(x, collector))
        # In Rails 4.0.0, DISTINCT was in a projection, whereas with 4.0.1
        # it is now stored in the set_quantifier. This moves it to the correct
        # place so the code works on both 4.0.0 and 4.0.1.
        if frag =~ /^\s*DISTINCT\s+/i
          core.set_quantifier = Arel::Nodes::Distinct.new
          frag.gsub!(/\s*DISTINCT\s+/, '')
        end
        frag
      end

      def select_statement_lock?
        @select_statement && @select_statement.lock
      end

      def source_with_lock_for_select_statement o, collector
        core = o.cores.first
        source = "FROM #{visit(core.source, collector).strip}" if core.source
        if source && o.lock
          lock = visit o.lock, a
          index = source.match(/FROM [\w\[\]\.]+/)[0].mb_chars.length
          source.insert index, " #{lock}"
        else
          source
        end
      end

      def table_from_select_statement(o)
        core = o.cores.first
        # TODO: [ARel 2.2] Use #from/#source vs. #froms
        # if Arel::Table === core.from
        #   core.from
        # elsif Arel::Nodes::SqlLiteral === core.from
        #   Arel::Table.new(core.from, @engine)
        # elsif Arel::Nodes::JoinSource === core.source
        #   Arel::Nodes::SqlLiteral === core.source.left ? Arel::Table.new(core.source.left, @engine) : core.source.left
        # end
        table_finder = lambda do |x|
          case x
          when Arel::Table
            x
          when Arel::Nodes::SqlLiteral
            Arel::Table.new(x, @engine)
          when Arel::Nodes::Join
            table_finder.call(x.left)
          end
        end
        table_finder.call(core.froms)
      end

      def single_distinct_select_statement?(o)
        projections = o.cores.first.projections
        p1 = projections.first
        projections.size == 1 &&
          ((p1.respond_to?(:distinct) && p1.distinct) ||
            p1.respond_to?(:include?) && p1.include?('DISTINCT'))
      end

      # Determine if the SELECT statement is asking for DISTINCT results,
      # but is using columns not part of the SELECT list in the ORDER BY.
      # This is necessary because SQL Server requires all ORDER BY entries
      # be in the SELECT list with DISTINCT. However, these ordering columns
      # can cause duplicate rows, which affect when using a limit.
      def distinct_non_present_orders? o, collector
        projections = o.cores.first.projections

        sq = o.cores.first.set_quantifier
        p1 = projections.first

        found_distinct = sq && sq.class.to_s =~ /Distinct/
        if (p1.respond_to?(:distinct) && p1.distinct) || (p1.respond_to?(:include?) && p1.include?('DISTINCT'))
          found_distinct = true
        end

        return false if !found_distinct || o.orders.uniq.empty?

        tables_all_columns = []
        expressions = projections.map do |p|
          visit(p, collector).split(',').map do |x|
            x.strip!
            # Rails 4.0.0 included DISTINCT in the first projection
            x.gsub!(/\s*DISTINCT\s+/, '')
            # Aliased column names
            x.gsub!(/\s+AS\s+\w+/i, '')
            # Identifier quoting
            x.gsub!(/\[|\]/, '')
            star_match = /^(\w+)\.\*$/.match(x)
            tables_all_columns << star_match[1] if star_match
            x.strip.downcase
          end.join(', ')
        end

        # Make sure each order by is in the select list, otherwise there needs
        # to be a subquery with row_numbe()
        o.orders.uniq.each do |order|
          order = visit(order, collector)
          order.strip!

          order.gsub!(/\s+(asc|desc)/i, '')
          # Identifier quoting
          order.gsub!(/\[|\]/, '')

          order.strip!
          order.downcase!

          # If we selected all columns from a table, the order is ok
          table_match = /^(\w+)\.\w+$/.match(order)
          next if table_match && tables_all_columns.include?(table_match[1])

          next if expressions.include?(order)

          return true
        end

        # We didn't find anything in the order by no being selected
        false
      end

      def windowed_single_distinct_select_statement?(o)
        o.limit &&
          o.offset &&
          single_distinct_select_statement?(o)
      end

      def single_distinct_select_everything_statement? o, collector
        single_distinct_select_statement?(o) &&
          visit(o.cores.first.projections.first, collector).ends_with?('.*')
      end

      def top_one_everything_for_through_join? o, collector
        single_distinct_select_everything_statement? o, collector &&
          (o.limit && !o.offset) &&
          join_in_select_statement?(o)
      end

      def all_projections_aliased_in_select_statement? o, collector
        projections = o.cores.first.projections
        projections.all? do |x|
          visit(x, collector).split(',').all? { |y| y.include?(' AS ') }
        end
      end

      def function_select_statement?(o)
        core = o.cores.first
        core.projections.any? { |x| Arel::Nodes::Function === x }
      end

      def eager_limiting_select_statement? o, collector
        core = o.cores.first
        single_distinct_select_statement?(o) &&
          (o.limit && !o.offset) &&
          core.groups.empty? &&
          !single_distinct_select_everything_statement?(o, collector)
      end

      def join_in_select_statement?(o)
        core = o.cores.first
        core.source.right.any? { |x| Arel::Nodes::Join === x }
      end

      def complex_count_sql?(o)
        core = o.cores.first
        core.projections.size == 1 &&
          Arel::Nodes::Count === core.projections.first &&
          o.limit &&
          !join_in_select_statement?(o)
      end

      def select_primary_key_sql?(o)
        core = o.cores.first
        return false if core.projections.size != 1
        p = core.projections.first
        t = table_from_select_statement(o)
        Arel::Attributes::Attribute === p && t.primary_key && t.primary_key.name == p.name
      end

      def find_and_fix_uncorrelated_joins_in_select_statement(o)
        core = o.cores.first
        # TODO: [ARel 2.2] Use #from/#source vs. #froms
        # return if !join_in_select_statement?(o) || core.source.right.size != 2
        # j1 = core.source.right.first
        # j2 = core.source.right.second
        # return unless Arel::Nodes::OuterJoin === j1 && Arel::Nodes::StringJoin === j2
        # j1_tn = j1.left.name
        # j2_tn = j2.left.match(/JOIN \[(.*)\].*ON/).try(:[],1)
        # return unless j1_tn == j2_tn
        # crltd_tn = "#{j1_tn}_crltd"
        # j1.left.table_alias = crltd_tn
        # j1.right.expr.left.relation.table_alias = crltd_tn
        return if !join_in_select_statement?(o) || !(Arel::Nodes::StringJoin === core.froms)
        j1 = core.froms.left
        j2 = core.froms.right
        return unless Arel::Nodes::OuterJoin === j1 && Arel::Nodes::SqlLiteral === j2 && j2.include?('JOIN ')
        j1_tn = j1.right.name
        j2_tn = j2.match(/JOIN \[(.*)\].*ON/).try(:[], 1)
        return unless j1_tn == j2_tn
        on_index = j2.index(' ON ')
        j2.insert on_index, " AS [#{j2_tn}_crltd]"
        j2.sub! "[#{j2_tn}].", "[#{j2_tn}_crltd]."
      end

      def rowtable_projections o, collector
        core = o.cores.first
        if windowed_single_distinct_select_statement?(o) && core.groups.blank?
          tn = table_from_select_statement(o).name
          core.projections.map do |x|
            x.dup.tap do |p|
              p.sub! 'DISTINCT', ''
              p.insert 0, visit(o.limit, collector) if o.limit
              p.gsub!(/\[?#{tn}\]?\./, '[__rnt].')
              p.strip!
            end
          end
        elsif single_distinct_select_statement?(o)
          tn = table_from_select_statement(o).name
          core.projections.map do |x|
            x.dup.tap do |p|
              p.sub! 'DISTINCT', "DISTINCT #{visit(o.limit, collector)}".strip if o.limit
              p.gsub!(/\[?#{tn}\]?\./, '[__rnt].')
              p.strip!
            end
          end
        elsif join_in_select_statement?(o) && all_projections_aliased_in_select_statement?(o, collector)
          core.projections.map do |x|
            Arel.sql visit(x, collector).split(',').map { |y| y.split(' AS ').last.strip }.join(', ')
          end
        elsif select_primary_key_sql?(o)
          [Arel.sql("[__rnt].#{quote_column_name(core.projections.first.name)}")]
        else
          [Arel.sql('[__rnt].*')]
        end
      end

      def rowtable_orders(o)
        if !o.orders.empty?
          o.orders
        else
          t = table_from_select_statement(o)
          c = t.primary_key || t.columns.first
          [c.asc]
        end.uniq
      end

      # TODO: We use this for grouping too, maybe make Grouping objects vs SqlLiteral.
      def projection_without_expression(projection, collector)
        Arel.sql(visit(projection, collector).split(',').map do |x|
          x.strip!
          x.sub!(/^(COUNT|SUM|MAX|MIN|AVG)\s*(\((.*)\))?/, '\3')
          x.sub!(/^DISTINCT\s*/, '')
          x.sub!(/TOP\s*\(\d+\)\s*/i, '')
          x.strip
        end.join(', '))
      end
    end
  end
end

Arel::Visitors::VISITORS['mssql'] = Arel::Visitors::VISITORS['sqlserver'] = Arel::Visitors::SQLServer
