class
    APPLICATION

create
  make

feature
    make
      local
          q: WORK_QUEUE
          qc: QUEUE_CONDITION
      do
        create qc.make
        create q.make (qc)
        q.enqueue (create {REQUEST})
        print (q.dequeue)
      end
end

