; *************** Eval ***************
%ptop.$ninstr$ = call i64**()* @getTopPtr()
%top.$ninstr$ = load i64** %ptop.$ninstr$
%tag.$ninstr$ = load i64* %top.$ninstr$

switch i64 %tag.$ninstr$, label %otherwise.$ninstr$ [ i64 1, label %NUM_EVAL.$ninstr$
                                                      i64 2, label %AP_EVAL.$ninstr$
                                                      i64 3, label %GLOB_EVAL.$ninstr$
                                                      i64 4, label %IND_EVAL.$ninstr$
                                                      i64 5, label %CONSTR_EVAL.$ninstr$ ]

NUM_EVAL.$ninstr$:
    br label %DONE_EVAL.$ninstr$

AP_EVAL.$ninstr$:
    call void()* @unwind()
    br label %DONE_EVAL.$ninstr$

GLOB_EVAL.$ninstr$:
    br label %DONE_EVAL.$ninstr$

IND_EVAL.$ninstr$:
    call i64*()* @pop()
    %paddr.$ninstr$ = call i64**(i64*)* @getAddrPtr(i64* %top.$ninstr$)
    %addr.$ninstr$ = load i64** %paddr.$ninstr$
    call void(i64*)* @push(i64* %addr.$ninstr$)
    call void()* @unwind()
    br label %DONE_EVAL.$ninstr$

CONSTR_EVAL.$ninstr$:
    br label %DONE_EVAL.$ninstr$

otherwise.$ninstr$:
    br label %DONE_EVAL.$ninstr$

DONE_EVAL.$ninstr$:

