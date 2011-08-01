declare i32 @printf(i8 *, ...)
declare i8* @malloc(i32)

; type declarations
%stack_item = type { %stack_item*, i32* }

; constants
@s = internal constant [6 x i8] c"ERROR\\00"
@snum = internal constant [4 x i8] c"%d\\0A\\00"
@NUM_TAG = global i32 1

; globals
@stack = global [1000 x i32*] undef
@sp = global i32 undef ; run-time stack pointer

define void @debug(i32 %x) {
    %ps = getelementptr [4 x i8]* @snum, i64 0, i64 0
    call i32(i8*, ...)* @printf(i8* %ps, i32 %x)

    ret void
}

define void @push(i32 %n) {
    %vsp = load i32* @sp
    %tmp = add i32 %n, 1
    %n1 = sub i32 %vsp, %tmp
    %ptop = getelementptr [1000 x i32*]* @stack, i32 0, i32 %vsp
    %pnth = getelementptr [1000 x i32*]* @stack, i32 0, i32 %n1
    %nth = load i32** %pnth

    ; store the nth element on top of the stack
    store i32* %nth, i32** %ptop

    ; update the stack pointer
    %vsp1 = add i32 %vsp, 1
    store i32 %vsp1, i32* @sp

    ret void
}

define void @pushint(i32 %n) {
    ; create the num node on the stack
    %temp = call i8*(i32)* @malloc(i32 8)
    %ptag = bitcast i8* %temp to i32*
    %pvtag = ptrtoint i32* %ptag to i64
    %pvval = add i64 4, %pvtag
    %pval = inttoptr i64 %pvval to i32*

    %numtag = load i32* @NUM_TAG
    store i32 %numtag, i32* %ptag
    store i32 %n, i32* %pval

    ; put address of newly allocated nodo to the stack
    %vsp = load i32* @sp
    %ptop = getelementptr [1000 x i32*]* @stack, i32 0, i32 %vsp

    store i32* %ptag, i32** %ptop

    ; update stack pointer
    %vsp1 = add i32 %vsp, 1
    store i32 %vsp1, i32* @sp

    ret void
}

define i32 @main() {
    call void()* @_main()
    ; tutaj teoretycznie powinien byc test czy zgadza sie liczba argumentow

    %vsp = load i32* @sp
    %index = sub i32 %vsp, 1
    %ptop = getelementptr [1000 x i32*]* @stack, i32 0, i32 %index

    %ptag = load i32** %ptop
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
