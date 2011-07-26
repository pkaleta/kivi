; ************* pushint $n$ ***************
%tmp.$reg$ = call i8* @malloc(i32 8)
%$reg$ = bitcast i8* %tmp.$reg$ to i32*
%ptagval.$reg$ = ptrtoint i32* %$reg$ to i64

; save tag
store i32 $tag$, i32* %$reg$

; save number
%pnumval.$reg$ = add i32 4, %ptagval.$reg$
%pnum.$reg$ = inttoptr i64 %pnumval.$reg$ to i32*
store i32 $n$, i32* %pnum.$reg$

