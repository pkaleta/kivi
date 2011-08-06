; *************** Pack ***************
%ptop.$ninstr$ = call i64** @getTopPtr()
%pconstr.$ninstr$ = call i64*(i64, i64**, i64)* @hAllocConstr(i64 $tag$, i64** %ptop.$ninstr$, i64 $arity$)
call void(i64)* @popn(i64 $arity$)
call void(i64*)* @push(i64* %pconstr.$ninstr$)

