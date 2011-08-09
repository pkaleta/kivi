; *************** Push $n$ ***************
%vsp.$ninstr$ = load i64* @sp
%tmp.$ninstr$ = add i64 $n$, 1
%n1.$ninstr$ = sub i64 %vsp.$ninstr$, %tmp.$ninstr$
%paddr.$ninstr$ = getelementptr [1000 x i64*]* @stack, i64 0, i64 %n1.$ninstr$
%addr.$ninstr$ = load i64** %paddr.$ninstr$

call void(i64*)* @push(i64* %addr.$ninstr$)

