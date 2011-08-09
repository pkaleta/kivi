; *************** $instr$ ***************
%a.$ninstr$ = call i64()* @popV()
%b.$ninstr$ = call i64()* @popV()
%res.$ninstr$ = $instr$ i64 %a.$ninstr$, %b.$ninstr$
call void(i64)* @pushV(i64 %res.$ninstr$)

