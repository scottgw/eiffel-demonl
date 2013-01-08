all:
	ec -config demon.ecf -target demon -c_compile
	EIFGENs/demon/W_code/demon
final:
	ec -config demon.ecf -target demon -c_compile -finalize

clean:
	rm -rf EIFGENs serializer.e work_queue_instr.e
