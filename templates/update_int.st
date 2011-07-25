    %ptr0 = call i8* @malloc(i32 8)
    %tagPtr = bitcast i8* %ptr0 to i32*
    %tagPtrVal = ptrtoint i32* %tagPtr to i64
    %valPtrVal = add i64 4, %tagPtrVal
    %valPtr = inttoptr i64 %valPtrVal to i32*
    %tag = add i32 $intTag$, 0
    store i32 %tag, i32* %tagPtr
    store i32 $value$, i32* %valPtr

