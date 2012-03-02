note
	description: "Summary description for {RANDOM_INT_REF}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	RANDOM_INT_REF

inherit
	V_INPUT_STREAM [INTEGER_REF]
		redefine
			default_create
		end

feature {NONE}
	rand: V_RANDOM

	default_create
		do
			create rand.set_seed (0)
		end

	off: BOOLEAN
		do
			Result := rand.off
		end

	forth
		do
			rand.forth
		end

	item: INTEGER_REF
		do
			create Result
			Result.set_item (rand.item)
		end


end
