%temp = call i8*(i32)* @malloc(i32 12)
%ptag = bitcast i8* %temp to i32*
%pvtag = ptrtoint i32* %ptag to i64
%pvar = add i64 %pvtag, 4
%par = inttoptr i64 %pvar to i32*
%pvcode = add i64 %pvtag, 8
%pcode = inttoptr i64 %pvcode to void()**

%globaltag = load i32* @GLOBAL_TAG
store i32 %globaltag, i32* %ptag
store i32 $arity$, i32* %par
store void()* @$name$, void()** %pcode
