note
	description: "Summary description for {WORK_QUEUE}."
	author: ""
	date: "$Date: 2012-01-18 10:08:30 +0100 (Wed, 18 Jan 2012) $"
	revision: "$Revision$"

class
	WORK_QUEUE

create
	make

feature -- {NON_EMPTY}
	set_done (d: BOOLEAN)
		do
			done := d
		end

	queue: S_QUEUE
	mutex: MUTEX

feature -- {NONE}
	done_or_not_empty: NON_EMPTY

feature
	make (non_empty: NON_EMPTY)
		do
			create queue
			create mutex.make

			done_or_not_empty := non_empty
			done_or_not_empty.set_work_queue (Current)

			done := False
		end

	done: BOOLEAN assign set_done

	count: INTEGER
		do
			mutex.lock

			Result := queue.count

			mutex.unlock
		end

	enqueue (req: REQUEST)
		do
			mutex.lock

			queue.enqueue (req)
			done_or_not_empty.check_inv

			mutex.unlock
		end

	dequeue2: REQUEST
		do
      queue.dequeue
      Result := queue.item
		ensure
      rely: queue.count = old queue.count 
      finished: done = (Result = Void)
		end


	dequeue: REQUEST
		do
			mutex.lock

			-- loop because condition variables can have spurious wakeups
			from
			until not queue.is_empty or done
			loop
				done_or_not_empty.make_step
			end

--			if not done then
--				Result := queue.item
--				queue.remove
--			end

			queue.dequeue
			Result := queue.item

			mutex.unlock
		ensure
      rely: mutex.is_set
--      finished: done = (Result = Void)
		end

  test
    do
      queue.dequeue
    end

	make_done
		do
			mutex.lock

			done := True
			done_or_not_empty.check_inv

			mutex.unlock
		end
end
