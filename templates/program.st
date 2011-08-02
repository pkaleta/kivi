declare i64 @printf(i8 *, ...)
declare i8* @malloc(i64)
declare i8* @memcpy(i8*, i8*, i64)


; constants
@s = internal constant [6 x i8] c"ERROR\\00"
@snum = internal constant [6 x i8] c"%lld\\0A\\00"
@NUM_TAG = global i64 1
@AP_TAG = global i64 2
@GLOBAL_TAG = global i64 3

; globals
@stack = global [1000 x i64*] undef
@sp = global i64 undef ; run-time stack pointer

define void @debug(i64 %x) {
    %ps = getelementptr [6 x i8]* @snum, i64 0, i64 0
    call i64(i8*, ...)* @printf(i8* %ps, i64 %x)

    ret void
}


; **************** Runtime stack operations

define void @push(i64* %addr) {
    ; store address on stack
    %vsp = load i64* @sp
    %ptop = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp
    store i64* %addr, i64** %ptop

    ; increment stack pointer
    %vsp1 = add i64 1, %vsp
    store i64 %vsp1, i64* @sp

    ret void
}


; *************** G-Machine operations

define void @GMPush(i64 %n) {
    %vsp = load i64* @sp
    %tmp = add i64 %n, 1
    %n1 = sub i64 %vsp, %tmp
    %paddr = getelementptr [1000 x i64*]* @stack, i64 0, i64 %n1
    %addr = load i64** %paddr

    call void(i64*)* @push(i64* %addr)

    ret void
}

define void @GMPop(i64 %n) {
    %vsp = load i64* @sp

    ; update the stack pointer
    %vsp1 = sub i64 %vsp, 1
    store i64 %vsp1, i64* @sp

    ret void
}

define void @GMPushint(i64 %n) {
    ; create the num node on the heap
    %temp = call i8*(i64)* @malloc(i64 16)
    %ptag = bitcast i8* %temp to i64*
    %pvtag = ptrtoint i64* %ptag to i64
    %pvval = add i64 8, %pvtag
    %pval = inttoptr i64 %pvval to i64*

    %numtag = load i64* @NUM_TAG
    store i64 %numtag, i64* %ptag
    store i64 %n, i64* %pval

    call void(i64*)* @push(i64* %ptag)

    ret void
}

define void @GMMkap() {
    %vsp = load i64* @sp
    %vsp1 = sub i64 %vsp, 1
    %vsp2 = sub i64 %vsp, 2
    %pa1 = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp1
    %a1 = load i64** %pa1
    %pa2 = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp2
    %a2 = load i64** %pa2

    ; create application node on the heap
    %temp = call i8*(i64)* @malloc(i64 24)
    %ptag = bitcast i8* %temp to i64*
    %pvtag = ptrtoint i64* %ptag to i64
    %pve1 = add i64 %pvtag, 8
    %pe1 = inttoptr i64 %pve1 to i64**
    %pve2 = add i64 %pvtag, 16
    %pe2 = inttoptr i64 %pve2 to i64**

    ; store the tag
    %aptag = load i64* @AP_TAG
    store i64 %aptag, i64* %ptag

    ; store addresses
    store i64* %a1, i64** %pe1
    store i64* %a2, i64** %pe2


;    %1 = load i64* %a2
;    call void(i64)* @debug(i64 100000)
;    call void(i64)* @debug(i64 %1)


    ; pop 2 elements from the stack
    store i64 %vsp2, i64* @sp

    call void(i64*)* @push(i64* %ptag)

    ret void
}

define void @GMUpdate(i64 %n) {
    %vsp = load i64* @sp
    %temp = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp
    %topAddr = load i64** %temp

    ; update the nth node on the stack to hold the same value as the top node
    %n1 = add i64 %n, 1
    %rootIndex = sub i64 %vsp, %n1
    %toUpdate = getelementptr [1000 x i64*]* @stack, i64 0, i64 %rootIndex
    store i64* %topAddr, i64** %toUpdate

    ret void
}

define void @GMEval() {
    %vsp = load i64* @sp
    %vsp1 = sub i64 %vsp, 1
    %ptr = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp1
    %addr = load i64** %ptr
    %tag = load i64* %addr

    switch i64 %tag, label %otherwise [ i64 1, label %NUM_EVAL
                                        i64 2, label %AP_EVAL
                                        i64 3, label %GLOB_EVAL ]

otherwise:
    br label %DONE_EVAL
NUM_EVAL:
    br label %DONE_EVAL

AP_EVAL:
    call void()* @GMUnwind()
    ret void

GLOB_EVAL:
    br label %DONE_EVAL

DONE_EVAL:

    ret void
}

define void @GMUnwind() {
    %vsp = load i64* @sp
    %vsp1 = sub i64 %vsp, 1
    %ptr = getelementptr [1000 x i64*]* @stack, i64 0, i64 %vsp1
    %ptag = load i64** %ptr
    %tag = load i64* %ptag
    call void(i64)* @debug(i64 %tag)

    switch i64 %tag, label %otherwise [ i64 1, label %NUM_UNWIND
                                        i64 2, label %AP_UNWIND
                                        i64 3, label %GLOB_UNWIND ]

NUM_UNWIND:
    br label %DONE_UNWIND

AP_UNWIND:
    %ap.pvtag = ptrtoint i64* %ptag to i64
    %pve1 = add i64 8, %ap.pvtag
    %pe1 = inttoptr i64 %pve1 to i64**
    %e1 = load i64** %pe1
    call void(i64*)* @push(i64* %e1)
    call void()* @GMUnwind()
    br label %DONE_UNWIND

GLOB_UNWIND:
    ; TODO: check for correct number of args, rearrange stack
    %glob.pvtag = ptrtoint i64* %ptag to i64
    %pvar = add i64 8, %glob.pvtag
    %par = inttoptr i64 %pvar to i64**
    %pvcode = add i64 16, %glob.pvtag
    %pcode = inttoptr i64 %pvcode to void()**
    %fun = load void()** %pcode
    call void()* %fun()
    br label %DONE_UNWIND

otherwise:
    br label %DONE_UNWIND

DONE_UNWIND:
    ret void
}


define i64 @main() {
    call void()* @_main()
    ; TODO: tutaj teoretycznie powinien byc test czy zgadza sie liczba argumentow

    %vsp = load i64* @sp
    %index = sub i64 %vsp, 1
    %ptop = getelementptr [1000 x i64*]* @stack, i64 0, i64 %index

    %ptag = load i64** %ptop
    %tag = load i64* %ptag

    switch i64 %tag, label %ERROR [i64 1, label %NUM]

ERROR:
    %pserr = getelementptr [6 x i8]* @s, i64 0, i64 0
    call i64 (i8 *, ...)* @printf(i8* %pserr)
;    %errorCode = add i32 0, 0
    ret i64 %tag
NUM:
    %psnum = getelementptr [6 x i8]* @snum, i64 0, i64 0
    %ptagval = ptrtoint i64* %ptag to i64
    %pnumval = add i64 4, %ptagval
    %pnum = inttoptr i64 %pnumval to i64*
    %num = load i64* %pnum
    call i64 (i8 *, ...)* @printf(i8* %psnum, i64 %num)
    ret i64 0
}

$scs$
