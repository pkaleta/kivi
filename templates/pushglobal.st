; *************** Pushglobal $name$ ***************
; allocate global node on the heap
%pglobal.$ninstr$ = call i64*(i64, void()*)* @hAllocGlobal(i64 $arity$, void()* @$name$)

; store function cell address on the stack
call void(i64*)* @push(i64* %pglobal.$ninstr$)

