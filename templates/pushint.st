; *************** Pushint $n$ ***************
; create the num node on the heap
%ptag.$ninstr$ = call i64*(i64)* @hAllocNum(i64 $n$)

; push node address onto the stack
call void(i64*)* @push(i64* %ptag.$ninstr$)

