deferred class
  SEXPR_SERIALIZER

inherit
  INTERNAL
  
feature
  temp_n: INTEGER
  extra_proc: PROCEDURE [ANY, TUPLE [ANY, STRING, SEXPR_SERIALIZER]]
  
  serialize (a_name: STRING;
             a_type: STRING;
             a_obj: ANY)
    local
      type_str: STRING
    do
      if a_obj = Void then
        add_def (a_name, a_type)
        add_null (a_name)
      else
        type_str := a_obj.generator

        if serial_map.has (a_obj) then
          add_var (a_name, serial_map.i_th (a_obj))
        else        
          serial_map.put (a_name, a_obj)
          -- print (a_obj.generator + "%N")
          if not a_obj.generating_type.is_expanded then
            add_non_null (a_name)
            add_def (a_name, type_str)
            serialize_ (a_obj, a_name)
          else
            if is_instance_of (a_obj, ({INTEGER}).type_id) then
              add_def (a_name, "Int")
            elseif is_instance_of (a_obj, ({BOOLEAN}).type_id) then
              add_def (a_name, "Bool")
            else
              print (a_obj.generator + "%N")
              check seralizer_unknown_expanded: False end
            end

            add_var (a_name, a_obj.out)
          end
        end
      end
    end

  serialize_ (obj: ANY; name: STRING)
    deferred
    end

  serialize_ref (subobj: ANY; parent_name, query_name, a_type_name: STRING)
    local
      name: STRING
      call: STRING
    do
      call := query_name + "(" + parent_name + ")"
      if attached subobj then
        if not serial_map.has (subobj) then
          name := new_temp_name
          serial_map.put (name, subobj)
          serialize_ (subobj, call)
        end
        add_non_null (call)
        name := serial_map.i_th (subobj)
        add_def (name, a_type_name)
        add_var (call, name)
      else
        add_null (call)
      end
    end
  
  new_temp_name: STRING
    do
      Result := "temp_" + count.out
      count := count + 1
    end

  count: INTEGER

  
  -- serialize_ (a_name: STRING; a_obj: ANY)
  --   local
  --     i: INTEGER
  --   do
  --     from i := 1
  --     until i > field_count (a_obj)
  --     loop
  --       serial_attr (a_name, a_obj,i )
  --       i := i + 1
  --     end

  --     extra_proc.call ([a_obj, a_name, Current])
  --   end

  -- serial_attr (a_name: STRING; a_obj: ANY; i: INTEGER)
  --   local
  --     type_index: INTEGER
  --     attr_expr_str: STRING
  --     ref: ANY
  --   do
  --     type_index := field_type (i, a_obj)
  --     attr_expr_str := attr_expr (a_name, a_obj, i)

  --     if type_index /= reference_type then
  --       add_var (attr_expr_str, attr_val (a_obj, i))
  --     else
  --       ref := field (i, a_obj)
  --       serialize_attr (ref, attr_expr_str)
  --     end
  --   end

  -- serialize_attr (attr: ANY; attr_field_name: STRING)
  --   local
  --     temp_name: STRING
  --   do
  --     if attr /= Void and then attr.generating_type.is_expanded then
  --       add_var (attr_field_name, attr.out)
  --     elseif not serial_map.has (attr) and
  --            not (attr = Void) and
  --            not ignored_class (attr) then
  --       temp_name := "temp" + temp_n.out
  --       temp_n := temp_n + 1
      
  --       add_non_null (temp_name)
  --       add_var (temp_name, attr_field_name)
  --       serialize (temp_name, attr)
  --     elseif serial_map.has (attr) and
  --            not (attr = Void) then
  --       add_var (attr_field_name, serial_map.i_th (attr)) 
  --     elseif attr = Void then
  --       add_null (attr_field_name)
  --     end
  --   end
  
  add_def (var: STRING; type: STRING)
    do
      definitions.extend (var + ": " + type)
    end
  
  add_var (var: STRING; value: STRING)
    do
      state.extend (var + " = " + value)
    end

  add_null (var: STRING)
    do
      add_var (var, null_str)
    end

  null_str: STRING = "null"
  
  add_non_null (var: STRING)
    do
      state.extend ("not (" + var + " = " + null_str + ")")
    end

  -- attr_val (a_obj: ANY; i: INTEGER): STRING
  --   do
  --     Result := field (i, a_obj).out
  --   end
  
  -- attr_expr (a_name: STRING; a_obj: ANY; i: INTEGER): STRING
  --   do
  --     Result := a_name + "." + full_name (a_obj, i)
  --   end
  
  -- full_name (a_obj: ANY; i: INTEGER): STRING
  --   do
  --     Result := a_obj.generator + "_" + field_name (i, a_obj)
  --   end

  
  serial_map: REF_EQ_TABLE [STRING, ANY]

  definitions: ARRAYED_LIST [STRING]
  state: ARRAYED_LIST [STRING]
end
