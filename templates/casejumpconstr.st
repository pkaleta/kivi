; *************** CasejumpConstr ***************
%ptop.$ninstr$ = call i64**()* @getTopPtr()
%top.$ninstr$ = load i64** %ptop.$ninstr$
%ptag.$ninstr$ = call i64*(i64*)* @getConstrTagPtr(i64* %top.$ninstr$)
%tag.$ninstr$ = load i64* %ptag.$ninstr$

switch i64 %tag.$ninstr$, label %DEFAULT.$ninstr$ [ $branches$ ]

$alts$

DEFAULT.$ninstr$:
    br label %END_CASE.$ninstr$

END_CASE.$ninstr$:

