    switch i32 %tag, label %EXIT [i32 1, label %NUM_UNWIND]

EXIT:
    %ps = getelementptr [6 x i8]* @s, i64 0, i64 0
    call i32 (i8 *, ...)* @printf(i8* %ps)
    %nullPtr = inttoptr i64 0 to i32*
    ret i32* %nullPtr

NUM_UNWIND:
    ret i32* %tagPtr
