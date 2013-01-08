class
  SERIALIZER

inherit
  SEXPR_SERIALIZER
create
  reset

feature {NONE}
  reset
    do
      create serial_map.make
      create state.make (10)
      create definitions.make (10)

      temp_n := 0
    end

end
