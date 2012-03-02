note
	description: "Summary description for {QUEUE_CONDITION}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	QUEUE_CONDITION [G]

inherit
	NON_EMPTY [G]

create
	make

feature

	make
		do
			create cond.make
		end

	cond: CONDITION_VARIABLE

	make_step
		do
			cond.wait (work_queue.mutex)
		end

	check_inv
		do
			cond.broadcast
		end

end
