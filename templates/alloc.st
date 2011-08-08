; *************** Alloc $n$ ***************
%pi.$ninstr$ = alloca i64
store i64 0, i64* %pi.$ninstr$
br label %LOOP.$ninstr$

LOOP.$ninstr$:
    %i.$ninstr$ = load i64* %pi.$ninstr$
    %cond.$ninstr$ = icmp eq i64 %i.$ninstr$, $n$
    br i1 %cond.$ninstr$, label %DONE_LOOP.$ninstr$, label %ALLOC.$ninstr$

ALLOC.$ninstr$:
    %node.$ninstr$ = call i64*(i64*)* @hAllocInd(i64* null)
    call void(i64*)* @push(i64* %node.$ninstr$)

    ; increment counter
    %i1.$ninstr$ = add i64 1, %i.$ninstr$
    store i64 %i1.$ninstr$, i64* %pi.$ninstr$
    br label %LOOP.$ninstr$

DONE_LOOP.$ninstr$:

