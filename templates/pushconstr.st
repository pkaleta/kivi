; *************** Pushconstr $tag$ $arity$***************
; TODO: update map so that the same constructor is not allocated twice

%pglobal.$ninstr$ = call i64*(i64, void()*)* @hAllocGlobal(i64 $arity$, void()* @_constr_$tag$_$arity$)
call void(i64*)* @push(i64* %pglobal.$ninstr$)

