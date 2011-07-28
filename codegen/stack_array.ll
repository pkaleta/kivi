declare i32 @printf(i8 *, ...)
@s = internal constant [6 x i8] c"%lld\0A\00"

%stack_item = type {%stack_item*, i32*}

;@sp = global %stack_item* null
@stack = global [1000 x i32*] undef
@sp = global i32 undef


define i32 @main() {
    store i32 1, i32* @sp


    %ptr1 = getelementptr [1000 x i32*]* @stack, i32 0, i32 0
    %item1 = alloca i32
    store i32 100, i32* %item1
    store i32* %item1, i32** %ptr1

    %ptr2 = getelementptr [1000 x i32*]* @stack, i32 0, i32 1
    %item2 = alloca i32
    store i32 200, i32* %item2
    store i32* %item2, i32** %ptr2


    %index = load i32* @sp

    %ptr = getelementptr [1000 x i32*]* @stack, i32 0, i32 %index
    %y = load i32** %ptr
    %z = load i32* %y
    ret i32 %z
    ret i32 0
}

