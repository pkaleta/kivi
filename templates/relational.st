; *************** $instr$ ***************
%a.$ninstr$ = call i64()* @popV()
%b.$ninstr$ = call i64()* @popV()
%cond.$ninstr$ = icmp $instr$ i64 %a.$ninstr$, %b.$ninstr$
br i1 %cond.$ninstr$, label %TRUE.$ninstr$, label %FALSE.$ninstr$

TRUE.$ninstr$:
    call void(i64)* @pushV(i64 $trueTag$)
    br label %END.$ninstr$

FALSE.$ninstr$:
    call void(i64)* @pushV(i64 $falseTag$)
    br label %END.$ninstr$

END.$ninstr$:

