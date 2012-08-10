class
    APPLICATION

create
  make

feature
    make
      local
          q: WORK_QUEUE [INTEGER]
          qc: QUEUE_CONDITION [INTEGER]
      do
        create qc.make
        create q.make (qc)
        q.enqueue (1)
        print (q.dequeue)
      end
end

