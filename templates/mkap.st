; *************** Mkap ***************
%fun.$ninstr$ = call i64*()* @pop()
%arg.$ninstr$ = call i64*()* @pop()

; create application node on the heap
%ap.$ninstr$ = call i64*(i64*, i64*)* @hAllocAp(i64* %fun.$ninstr$, i64* %arg.$ninstr$)

; push the newly allocated appliation node address onto the stack
call void(i64*)* @push(i64* %ap.$ninstr$)

