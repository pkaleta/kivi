define i32 @main() {
    %x = alloca i32
    store i32 3, i32* %x
    %y = alloca i32
    ret i32 0
}

