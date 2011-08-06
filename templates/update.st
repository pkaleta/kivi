; *************** Update $n$ ***************
%top.$ninstr$ = call i64*()* @pop()

; update the nth node on the stack to hold the same value as the top node
%vsp.$ninstr$ = load i64* @sp
%n1.$ninstr$ = add i64 $n$, 1
%rootIndex.$ninstr$ = sub i64 %vsp.$ninstr$, %n1.$ninstr$
%toUpdate.$ninstr$ = call i64**(i64)* @getItemPtr(i64 %rootIndex.$ninstr$)

; create ind node on the heap
%ind.$ninstr$ = call i64*(i64*)* @hAllocInd(i64* %top.$ninstr$)

store i64* %ind.$ninstr$, i64** %toUpdate.$ninstr$

