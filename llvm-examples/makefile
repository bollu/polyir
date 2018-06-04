FILE=scev-2d
PO="/home/bollu/build/llvm/build/bin/opt"

scev:create_ll
	$(PO) -analyze -scalar-evolution $(FILE).ll

create_ll:
	/home/bollu/build/llvm/llvm/tools/polly/test/create_ll.sh $(FILE).c


runscops:
	$(PO) -polly-use-llvm-names -polly-process-unprofitable -analyze -polly-scops $(FILE).ll


rundeps:
	$(PO) -polly-use-llvm-names -polly-process-unprofitable -analyze -polly-dependences $(FILE).ll


runcfg:
	$(PO) -polly-use-llvm-names -polly-process-unprofitable -analyze -polly-dot-cfg $(FILE).ll



