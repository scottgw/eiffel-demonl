class TEST

feature
    a: INTEGER

    change_a
      require
          a > 0
      do
          a := a * 2
      ensure
          a = old a * 2
      end


    test1
      do
        change_a
        change_a
      ensure
        a = old a + 9
      end

    test2
      do
        if 0 = 0 then
        elseif 1 = 0 then
        else
        end
      ensure
        a > 42
      end
end
