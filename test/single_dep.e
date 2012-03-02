note
	description: "Summary description for {SINGLE_DEP}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

deferred class
	SINGLE_DEP

feature
	check_inv
		require
			inv
		deferred
		end

	inv: BOOLEAN
		deferred
		end

	make_step
		deferred
		ensure
			inv
		end

end
