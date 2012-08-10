note
	description: "Summary description for {WORK_QUEUE}."
	author: ""
	date: "$Date: 2012-01-18 10:08:30 +0100 (Wed, 18 Jan 2012) $"
	revision: "$Revision$"

class
	WORK_QUEUE [G]

create
	make

feature {NON_EMPTY}
	set_done (d: BOOLEAN)
		do
			done := d
		end

	queue: S_QUEUE [G]
	mutex: MUTEX

feature {NONE}
	done_or_not_empty: NON_EMPTY [G]


feature
	make (non_empty: NON_EMPTY [G])
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

	enqueue (req: G)
		do
			mutex.lock

			queue.enqueue (req)
			done_or_not_empty.check_inv

			mutex.unlock
		end

	dequeue: G
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

			Result := queue.item
			queue.dequeue

			mutex.unlock
		ensure
            rely: True or False
            finished: done = (Result = Void)
		end

	make_done
		do
			mutex.lock

			done := True
			done_or_not_empty.check_inv

			mutex.unlock
		end
end
