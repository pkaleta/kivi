; ************* mkap ***************
%tmp.$reg$ = call i8* @malloc(i32 12)
%$reg$ = bitcast i8* %tmp$reg$ to i32*
store i32 $tag$, i32* %$reg$

%ptagval.$reg$ = ptrtoint i32* %$reg$ to i64

%pe1val.$reg$ = add i64 4, %ptagval.$reg$
%pe1.$reg$ = inttoptr i64 %pe1val.$reg$ to i32*
store i32 $e1$, i32* %pe1.$reg$

%pe2val.$reg$ = add i64 8, %ptagval.$reg$
%pe2.$reg$ = inttoptr i64 %pe2val.$reg$ to i32*
store i32 $e2$, i32* %pe2.$reg$

