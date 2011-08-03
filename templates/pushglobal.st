%temp = call i8*(i64)* @malloc(i64 24)
%ptag = bitcast i8* %temp to i64*
%pvtag = ptrtoint i64* %ptag to i64
%pvar = add i64 %pvtag, 8
%par = inttoptr i64 %pvar to i64*
%pvcode = add i64 %pvtag, 16
%pcode = inttoptr i64 %pvcode to void()**

%globaltag = load i64* @GLOBAL_TAG
store i64 %globaltag, i64* %ptag
store i64 $arity$, i64* %par
store void()* @$name$, void()** %pcode

; store function cell address on the stack
call void(i64*)* @push(i64* %ptag)

