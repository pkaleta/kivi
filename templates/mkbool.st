; *************** MkBool ***************
%n.$ninstr$ = call i64()* @popV()

; alloc num node on the heap
%bool.$ninstr$ = call i64*(i64, i64, i64**)* @hAllocConstr(i64 %n.$ninstr$, i64 0, i64** null)

; push address onto the stack
call void(i64*)* @push(i64* %bool.$ninstr$)

