declare i32 @printf(i8 *, ...)
declare i8* @malloc(i32)

; type declarations
%stack_item = type { %stack_item*, i32* }

; constants
@s = internal constant [6 x i8] c"ERROR\\00"
@snum = internal constant [4 x i8] c"%d\\0A\\00"

; globals
@sp = %stack_item* null ; run-time stack pointer


define void @push(%stack_item* %item, i32* %addr) {
    %pprev = call %stack_item**(%stack_item*)* @get_prev(%stack_item* %%item)
    %paddr = call i32**(%stack_item*)* @get_addr(%stack_item* %%item)

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
    %ptag = call i32* (i32)* @_main(i32 0)
    ; tutaj teoretycznie powinien byc test czy zgadza sie liczba argumentow
    %tag = load i32* %ptag

    switch i32 %tag, label %ERROR [i32 1, label %NUM]

ERROR:
    %pserr = getelementptr [6 x i8]* @s, i64 0, i64 0
    call i32 (i8 *, ...)* @printf(i8* %pserr)
    %errorCode = add i32 0, 0
    ret i32 %errorCode
NUM:
    %psnum = getelementptr [4 x i8]* @snum, i64 0, i64 0
    %ptagval = ptrtoint i32* %ptag to i64
    %pnumval = add i64 4, %ptagval
    %pnum = inttoptr i64 %pnumval to i32*
    %num = load i32* %pnum
    call i32 (i8 *, ...)* @printf(i8* %psnum, i32 %num)
    ret i32 0
}

$scs$
