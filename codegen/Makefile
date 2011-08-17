all:
	llvm-as -f test.ll
	llc test.bc
	clang test.s -L/usr/lib64/erlang/lib/erl_interface-3.6.5/lib/ -lerl_interface -lei -lpthread -otest
