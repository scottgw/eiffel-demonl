class REF_EQ_TABLE [V -> detachable ANY, K]

create
  make
  
feature
  make
    do
      create keys.make (10)
      create values.make (10)
    end

  put (v: V; k: K)
    local
      i: INTEGER
    do
      i := index_of (k)

      if i = 0 then
        keys.extend (k)
        values.extend (v)
      else
        values [i] := v
      end
    end

  has (k: K): BOOLEAN
    do
      Result := index_of (k) /= 0
    ensure
      non_zero_index: Result = (index_of (k) /= 0)
    end
  
  i_th (k: K): V
    require
      has_key: has (k)
    local
      i: INTEGER
    do
      i := index_of (k)
      Result := values [i]
    end

  index_of (k: K): INTEGER
    local
      i: INTEGER
    do
      i := keys.index

      keys.search (k)

      if keys.exhausted then
        Result := 0
      else
        Result := keys.index
      end

      keys.go_i_th (i)
    end

feature {NONE}
  keys: ARRAYED_LIST [K]
  values: ARRAYED_LIST [V]
end
