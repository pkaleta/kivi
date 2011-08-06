; *************** MkInt ***************
%n.$ninstr$ = call i64()* @popV()

; alloc num node on the heap
%num.$ninstr$ = call i64*(i64)* @hAllocNum(i64 %n.$ninstr$)

; push address onto the stack
call void(i64*)* @push(i64* %num.$ninstr$)

