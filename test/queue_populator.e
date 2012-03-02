note
	description: "Summary description for {QUEUE_POPULATOR}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	QUEUE_POPULATOR [G]

inherit
	NON_EMPTY [G]

create
	make

feature
	doner: V_RANDOM

	make (g: V_INPUT_STREAM [G])
		do
			gen := g
			create doner.set_seed (0)
		end

	gen: V_INPUT_STREAM [G]

	make_step
		do
			work_queue.queue.extend (gen.item)
			work_queue.done := doner.fair_bit
			doner.forth
			gen.forth
		end


	check_inv
		do
			check inv end
		end

end
