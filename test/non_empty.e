note
	description: "Summary description for {NON_EMPTY}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

deferred class
	NON_EMPTY

inherit
	SINGLE_DEP

feature

	work_queue: WORK_QUEUE

	set_work_queue (w: WORK_QUEUE)
		do
			work_queue := w
		end

	inv: BOOLEAN
		do
			Result := not work_queue.queue.is_empty
		ensure then
			Result = not work_queue.queue.is_empty
		end
end
