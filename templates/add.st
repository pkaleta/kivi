; *************** Add ***************
%a.$ninstr$ = call i64()* @popV()
%b.$ninstr$ = call i64()* @popV()
%res.$ninstr$ = add i64 %a.$ninstr$, %b.$ninstr$
call void(i64)* @pushV(i64 %res.$ninstr$)

