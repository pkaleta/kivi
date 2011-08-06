; *************** Get ***************
%top.$ninstr$ = call i64*()* @pop()
%tag.$ninstr$ = call i64(i64*)* @getTag(i64* %top.$ninstr$)

switch i64 %tag.$ninstr$, label %NOT_FOUND.$ninstr$ [ i64 1, label %NUM.$ninstr$ ]

NUM.$ninstr$:
    %pnum.$ninstr$ = call i64*(i64*)* @getNumPtr(i64* %top.$ninstr$)
    %num.$ninstr$ = load i64* %pnum.$ninstr$

    call void(i64)* @pushV(i64 %num.$ninstr$)
    br label %DONE_GET.$ninstr$

NOT_FOUND.$ninstr$:
    %ps.$ninstr$ = getelementptr [63 x i8]* @getErrStr, i64 0, i64 0
    call i64 (i8 *, ...)* @printf(i8* %ps.$ninstr$)
    br label %DONE_GET.$ninstr$

DONE_GET.$ninstr$:


