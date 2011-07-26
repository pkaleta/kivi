; ************* pushglobal $v$ ***************
%tmp.$reg$ = call i8* @malloc(i32 12)
%$reg$ = bitcast i8* %tmp.$reg$ to i32*
%ptagval.$reg$ = ptrtoint i32* %$reg$ to i64

; save the tag
store i32 $tag$, i32* %$reg$

; save number of args
%pargsval.$reg$ = add i32 4, %ptagval.$reg$
%pargs.$reg$ = inttoptr i64 %pargsval.$reg$ to i32*
store i32 $args$, i32* %pargs.$reg$

; save pointer to function
%pfunval.$reg$ = add i32 8, %ptagval.$reg$
%pfun.$reg$ = inttoptr i64 %pfunval.$reg$ to i32()**
store i32()* @$v$, i32()** %pfun.$reg$

