; *************** CasejumpSimple ***************
%ptop.$ninstr$ = call i64**()* @getTopPtr()
%top.$ninstr$ = load i64** %ptop.$ninstr$
%pnum.$ninstr$ = call i64*(i64*)* @getNumPtr(i64* %top.$ninstr$)
%num.$ninstr$ = load i64* %pnum.$ninstr$

switch i64 %num.$ninstr$, label %ALT-1.$ninstr$ [ $branches$ ]

$alts$

DEFAULT.$ninstr$:
    br label %END_CASE.$ninstr$

END_CASE.$ninstr$:

