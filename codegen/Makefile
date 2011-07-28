all:
	llvm-as -f test.ll
	llc test.bc
	llvm-gcc -o test test.s
