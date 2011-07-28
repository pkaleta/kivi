declare i32 @printf(i8 *, ...)
@s = internal constant [6 x i8] c"%lld\0A\00"

%stack_item = type {%stack_item*, i32*}

@sp = global %stack_item* null


define void @debug(i64 %x) {
    %ps = getelementptr [6 x i8]* @s, i64 0, i64 0
    call i32(i8*, ...)* @printf(i8* %ps, i64 %x);

    ret void
}


define void @push(%stack_item* %item, i32* %addr) {
    %pprev = call %stack_item**(%stack_item*)* @get_prev(%stack_item* %item)
    %paddr = call i32**(%stack_item*)* @get_addr(%stack_item* %item)

    %ptop = load %stack_item** @sp
    store %stack_item* %ptop, %stack_item** %pprev
    store i32* %addr, i32** %paddr

    store %stack_item* %item, %stack_item** @sp

    ret void
}

define i32* @pop() {
    %sp = load %stack_item** @sp
    %pprev = call %stack_item**(%stack_item*)* @get_prev(%stack_item* %sp)
    %paddr = call i32**(%stack_item*)* @get_addr(%stack_item* %sp)

    %prev = load %stack_item** %pprev
    store %stack_item* %prev, %stack_item** @sp

    %addr = load i32** %paddr
    ret i32* %addr
}

define %stack_item** @get_prev(%stack_item* %item) {
    %pprev = getelementptr %stack_item* %item, i32 0, i32 0
    ret %stack_item** %pprev
}

define i32** @get_addr(%stack_item* %item) {
    %paddr = getelementptr %stack_item* %item, i32 0, i32 1
    ret i32** %paddr
}


define i32 @main() {
    %item = alloca %stack_item
    %x = alloca i32
    store i32 100, i32* %x
    call void(%stack_item*, i32*)* @push(%stack_item* %item, i32* %x)

    %item1 = alloca %stack_item
    %y = alloca i32
    store i32 200, i32* %y
    call void(%stack_item*, i32*)* @push(%stack_item* %item1, i32* %y)

    %item2 = alloca %stack_item
    %z = alloca i32
    store i32 55, i32* %z
    call void(%stack_item*, i32*)* @push(%stack_item* %item2, i32* %z)

    call i32*()* @pop()
    call i32*()* @pop()

    %sp = load %stack_item** @sp
    %val = call i32**(%stack_item*)* @get_addr(%stack_item* %sp)
    %val0 = load i32** %val
    %val1 = load i32* %val0

    ret i32 %val1
}


;define i32 @main() {
;    %x = alloca i32
;    store i32 3, i32* %x
;    %y = getelementptr i32* %x
;
;    store i32 4, i32* %y
;
;    %val = load i32* %x
;    call void(i32)* @debug(i32 %val)
;
;    ret i32 0
;}

