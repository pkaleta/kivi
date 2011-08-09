; *************** Pop $n$ ***************
%vsp.$ninstr$ = load i64* @sp

; update the stack pointer
%vsp1.$ninstr$ = sub i64 %vsp.$ninstr$, $n$
store i64 %vsp1.$ninstr$, i64* @sp

