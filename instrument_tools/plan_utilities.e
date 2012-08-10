class
  PLAN_UTILITIES
  
feature
  rely_call (line: INTEGER;
             a_objs: ARRAY [TUPLE[name: STRING; obj: ANY]];
             goal_str: STRING;
             rely_str: STRING;
             extra_proc: PROCEDURE [ANY, TUPLE [ANY, STRING, SEXPR_SERIALIZER]])
    local
      i: INTEGER
      str: STRING
      serizer: SEXPR_SERIALIZER
    do
      create serizer.reset (extra_proc)
      str := ""
      
      from i := 1
      until i > a_objs.count
      loop
        serizer.serialize (a_objs [i].name, a_objs [i].obj)
        i := i + 1
      end

      across serizer.definitions as dc loop
        str := str + dc.item + "%N"
      end

      across serizer.state as sc loop
        str := str + sc.item + "%N"
      end

      str := str + "@" + num_steps.out + "->%N"
      str := str + "%T(not (" + goal_str + ")) and %N"
      str := str + "%T(" + rely_str + ")%N"

      write_goal (str.string, line)
      inc_num
    end

feature {NONE}
  write_goal (str: STRING; line: INTEGER)
    local
      file: PLAIN_TEXT_FILE
    do
      create file.make_open_write (file_name (line))
      file.put_string (str)
      file.flush
      file.close
    end

  file_num_cell: CELL [INTEGER]
    once
      create Result.put (0)
    end

  inc_num
    do
      file_num_cell.put (file_num_cell.item + 1)
    end

  file_name (line: INTEGER): STRING
    do
      check file_name_pos: file_num_cell.item >= 0 end
      Result := "goal_file-line-" + line.out + "-" +
        file_num_cell.item.out + ".goal"
    end

  
  print_time
    local
      time: TIME
    do
      create time.make_now
      print (time.out + "%N")
    end
  
  num_steps: INTEGER = 3

end

