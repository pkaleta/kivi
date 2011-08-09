; *************** Select $n$ $k$ ***************
%pconstr.$ninstr$ = call i64*()* @pop()

; we assume that element on the top of the stack is a constructor
%pargs.$ninstr$ = call i64**(i64*)* @getConstrArgsPtr(i64* %pconstr.$ninstr$)

%parg.$ninstr$ = call i64**(i64, i64**)* @incPtr(i64 $k$, i64** %pargs.$ninstr$)
%arg.$ninstr$ = load i64** %parg.$ninstr$

call void(i64*)* @push(i64* %arg.$ninstr$)

