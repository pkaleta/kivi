declare i64 @printf(i8 *, ...)
declare i8* @malloc(i64)
declare i8* @memcpy(i8*, i8*, i64)


$erlang()$


; constants
@getErrStr = internal constant [63 x i8] c"ERROR: Item different than expected found while running GMGet\\0A\\00"
@s = internal constant [7 x i8] c"ERROR\\0A\\00"
@snum = internal constant [6 x i8] c"%lld \\00"
@sconstr = internal constant [13 x i8] c"(Constr %d: \\00"
@snl = internal constant [2 x i8] c"\\0A\\00"
@srbr = internal constant [2 x i8] c")\\00"
@NUM_TAG = global i64 1
@AP_TAG = global i64 2
@GLOBAL_TAG = global i64 3
@IND_TAG = global i64 4
@CONSTR_TAG = global i64 5

; globals
@vstack = global [1000 x i64] undef
@vsp = global i64 undef

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
    %n = load i64* @sp
    %ptop = call i64**(i64)* @getItemPtr(i64 %n)
    store i64* %addr, i64** %ptop

    ; increment stack pointer
    call void(i64*)* @incSp(i64* @sp)

    ret void
}

define i64* @pop() {
    %ptop = call i64**()* @getTopPtr()
    %addr = load i64** %ptop

    call void(i64*)* @decSp(i64* @sp)

    ret i64* %addr
}

; pops n elements from the top of the stack
define void @popn(i64 %n) {
    %vsp = load i64* @sp
    %vsp1 = sub i64 %vsp, %n
    store i64 %vsp1, i64* @sp

    ret void
}

define i64** @getTopPtr() {
    %n = load i64* @sp
    %n1 = sub i64 %n, 1
    %topPtr = call i64**(i64)* @getItemPtr(i64 %n1)

    ret i64** %topPtr
}

define i64** @getItemPtr(i64 %n) {
    %item = getelementptr [1000 x i64*]* @stack, i64 0, i64 %n

    ret i64** %item
}


; **************** Runtime vstack operations

define void @pushV(i64 %val) {
    ; store address on stack
    %n = load i64* @vsp
    %ptop = call i64*(i64)* @getItemVPtr(i64 %n)
    store i64 %val, i64* %ptop

    ; increment stack pointer
    call void(i64*)* @incSp(i64* @vsp)

    ret void
}

define i64 @popV() {
    %ptop = call i64*()* @getTopVPtr()
    %val = load i64* %ptop

    call void(i64*)* @decSp(i64* @vsp)

    ret i64 %val
}

define i64* @getTopVPtr() {
    %n = load i64* @vsp
    %n1 = sub i64 %n, 1
    %item = call i64*(i64)* @getItemVPtr(i64 %n1)

    ret i64* %item
}

define i64* @getItemVPtr(i64 %n) {
    %ptr = getelementptr [1000 x i64]* @vstack, i64 0, i64 %n

    ret i64* %ptr
}

; **************** Generic stack operations

define void @incSp(i64* %sp) {
    %n = load i64* %sp
    %n1 = add i64 %n, 1
    store i64 %n1, i64* %sp

    ret void
}

define void @decSp(i64* %sp) {
    %n = load i64* %sp
    %n1 = sub i64 %n, 1
    store i64 %n1, i64* %sp

    ret void
}


; *************** Heap allocation functions

define i64* @hAllocNum(i64 %n) {
    %ptr = call i8*(i64)* @malloc(i64 16)
    %ptag = bitcast i8* %ptr to i64*
    %pval = call i64*(i64*)* @getNumPtr(i64* %ptag)

    %numtag = load i64* @NUM_TAG
    store i64 %numtag, i64* %ptag
    store i64 %n, i64* %pval

    ret i64* %ptag
}

define i64* @hAllocAp(i64* %a1, i64* %a2) {
    %ptr = call i8*(i64)* @malloc(i64 24)
    %ptag = bitcast i8* %ptr to i64*
    %pfun = call i64**(i64*)* @getFunPtr(i64* %ptag)
    %parg = call i64**(i64*)* @getArgPtr(i64* %ptag)

    ; store the tag
    %aptag = load i64* @AP_TAG
    store i64 %aptag, i64* %ptag

    ; store addresses
    store i64* %a1, i64** %pfun
    store i64* %a2, i64** %parg

    ret i64* %ptag
}

define i64* @hAllocGlobal(i64 %arity, void()* %funPtr) {
    %ptr = call i8*(i64)* @malloc(i64 24)
    %ptag = bitcast i8* %ptr to i64*
    %parity = call i64*(i64*)* @getArityPtr(i64* %ptag)
    %pcode = call void()**(i64*)* @getCodePtr(i64* %ptag)

    ; save the tag
    %globaltag = load i64* @GLOBAL_TAG
    store i64 %globaltag, i64* %ptag

    store i64 %arity, i64* %parity
    store void()* %funPtr, void()** %pcode

    ret i64* %ptag
}

define i64* @hAllocInd(i64* %addr) {
    %ptr = call i8*(i64)* @malloc(i64 16)
    %ptag = bitcast i8* %ptr to i64*
    %paddr = call i64**(i64*)* @getAddrPtr(i64* %ptag)

    ;save the tag
    %indtag = load i64* @IND_TAG
    store i64 %indtag, i64* %ptag

    ; save address
    store i64* %addr, i64** %paddr

    ret i64* %ptag
}

define i64** @incPtr(i64 %n, i64** %ptr) {
    %val = ptrtoint i64** %ptr to i64
    %tmp = mul i64 %n, 8
    %incval = add i64 %val, %tmp
    %incptr = inttoptr i64 %incval to i64**

    ret i64** %incptr
}

define i64** @decPtr(i64 %n, i64** %ptr) {
    %val = ptrtoint i64** %ptr to i64
    %tmp = mul i64 %n, 8
    %incval = sub i64 %val, %tmp
    %decptr = inttoptr i64 %incval to i64**

    ret i64** %decptr
}

define i64* @hAllocConstr(i64 %tag, i64 %nargs, i64** %psrcStart) {
    %argsSize = mul i64 %nargs, 8
    %size = add i64 24, %argsSize
    %ptr = call i8*(i64)* @malloc(i64 %size)
    %pconstr = bitcast i8* %ptr to i64*
    %ptag = call i64*(i64*)* @getConstrTagPtr(i64* %pconstr)
    %parity = call i64*(i64*)* @getConstrArityPtr(i64* %pconstr)
    %pdestStart = call i64**(i64*)* @getConstrArgsPtr(i64* %pconstr)

    ; store node tag
    %t = load i64* @CONSTR_TAG
    store i64 %t, i64* %pconstr

    ; store arity
    store i64 %nargs, i64* %parity

    ; store constructor tag
    store i64 %tag, i64* %ptag

    ; store arguments
    %pi = alloca i64
    store i64 0, i64* %pi

    %curpsrc = alloca i64**
    store i64** %psrcStart, i64*** %curpsrc
    %curpdest = alloca i64**
    store i64** %pdestStart, i64*** %curpdest
    br label %LOOP
LOOP:
    %i = load i64* %pi
    %cond = icmp eq i64 %i, %nargs
    br i1 %cond, label %DONE_LOOP, label %COPY
COPY:
    ; copy current argument pointer
    %psrc = load i64*** %curpsrc
    %src = load i64** %psrc
    %pdest = load i64*** %curpdest
    store i64* %src, i64** %pdest

    ; increment both pointers
    %psrc1 = call i64**(i64, i64**)* @decPtr(i64 1, i64** %psrc)
    store i64** %psrc1, i64*** %curpsrc
    %pdest1 = call i64**(i64, i64**)* @incPtr(i64 1, i64** %pdest)
    store i64** %pdest1, i64*** %curpdest

    ; increment counter
    %i1 = add i64 1, %i
    store i64 %i1, i64* %pi
    br label %LOOP

DONE_LOOP:
    ret i64* %pconstr
}


; *************** Utility functions

define i64 @getTag(i64* %addr) {
    %tag = load i64* %addr

    ret i64 %tag
}

define i64* @getNumPtr(i64* %addr) {
    %p8num = call i8*(i64, i64*)* @nextPtr(i64 1, i64* %addr)
    %pnum = bitcast i8* %p8num to i64*

    ret i64* %pnum
}

define i64** @getFunPtr(i64* %addr) {
    %p8fun = call i8*(i64, i64*)* @nextPtr(i64 1, i64* %addr)
    %pfun = bitcast i8* %p8fun to i64**

    ret i64** %pfun
}

define i64** @getArgPtr(i64* %addr) {
    %p8arg = call i8*(i64, i64*)* @nextPtr(i64 2, i64* %addr)
    %parg = bitcast i8* %p8arg to i64**

    ret i64** %parg
}

define i64* @getArityPtr(i64* %addr) {
    %p8arity = call i8*(i64, i64*)* @nextPtr(i64 1, i64* %addr)
    %parity = bitcast i8* %p8arity to i64*

    ret i64* %parity
}

define void()** @getCodePtr(i64* %addr) {
    %p8code = call i8*(i64, i64*)* @nextPtr(i64 2, i64* %addr)
    %pcode = bitcast i8* %p8code to void()**

    ret void()** %pcode
}

define i64** @getAddrPtr(i64* %addr) {
    %p8addr = call i8*(i64, i64*)* @nextPtr(i64 1, i64* %addr)
    %paddr = bitcast i8* %p8addr to i64**

    ret i64** %paddr
}

define i64* @getConstrTagPtr(i64* %addr) {
    %p8tag = call i8*(i64, i64*)* @nextPtr(i64 1, i64* %addr)
    %ptag = bitcast i8* %p8tag to i64*

    ret i64* %ptag
}

define i64* @getConstrArityPtr(i64* %addr) {
    %p8tag = call i8*(i64, i64*)* @nextPtr(i64 2, i64* %addr)
    %ptag = bitcast i8* %p8tag to i64*

    ret i64* %ptag
}

define i64** @getConstrArgsPtr(i64* %addr) {
    %p8args = call i8*(i64, i64*)* @nextPtr(i64 3, i64* %addr)
    %pargs = bitcast i8* %p8args to i64**

    ret i64** %pargs
}

define i8* @nextPtr(i64 %n, i64* %ptr) {
    %1 = ptrtoint i64* %ptr to i64
    %2 = mul i64 %n, 8
    %3 = add i64 %2, %1
    %4 = inttoptr i64 %3 to i8*
    ret i8* %4
}

; *************** G-Machine operations

define void @rearrange(i64 %arity) {
    %vsp = load i64* @sp
    %vsp1 = sub i64 %vsp, 1
    %item = alloca i64
    store i64 %vsp1, i64* %item

    %pi = alloca i64
    store i64 0, i64* %pi
    br label %LOOP
LOOP:
    %i = load i64* %pi
    %cond = icmp ne i64 %i, %arity
    ; tests if i equals arity
    br i1 %cond, label %NEXT_ELEM, label %END
NEXT_ELEM:
    ; increment counter
    %j = add i64 1, %i
    store i64 %j, i64* %pi

    ; rearrange item
    %cur = load i64* %item
    %cur1 = sub i64 %cur, 1
    %pap = call i64**(i64)* @getItemPtr(i64 %cur1)
    %ap = load i64** %pap
    %pvtag = ptrtoint i64* %ap to i64
    %pve2 = add i64 16, %pvtag
    %pe2 = inttoptr i64 %pve2 to i64**
    %e2 = load i64** %pe2

    %pcur = call i64**(i64)* @getItemPtr(i64 %cur)
    store i64* %e2, i64** %pcur

    ; get next element in the stack
    store i64 %cur1, i64* %item


    br label %LOOP

END:
    ret void
}


define void @eval() {
    %ptop = call i64**()* @getTopPtr()
    %top = load i64** %ptop
    %tag = load i64* %top

    switch i64 %tag, label %otherwise [ i64 1, label %NUM_EVAL
                                        i64 2, label %AP_EVAL
                                        i64 3, label %GLOB_EVAL
                                        i64 4, label %IND_EVAL
                                        i64 5, label %CONSTR_EVAL ]

NUM_EVAL:
    br label %DONE_EVAL

AP_EVAL:
    call void()* @unwind()
    br label %DONE_EVAL

GLOB_EVAL:
    call void()* @unwind()
    br label %DONE_EVAL

IND_EVAL:
    call i64*()* @pop()
    %paddr = call i64**(i64*)* @getAddrPtr(i64* %top)
    %addr = load i64** %paddr
    call void(i64*)* @push(i64* %addr)
    call void()* @unwind()
    br label %DONE_EVAL

CONSTR_EVAL:
    br label %DONE_EVAL

otherwise:
    br label %DONE_EVAL

DONE_EVAL:
    ret void
}


define void @unwind() {
    %ptop = call i64**()* @getTopPtr()
    %top = load i64** %ptop
    %tag = load i64* %top

    switch i64 %tag, label %otherwise [ i64 1, label %NUM_UNWIND
                                        i64 2, label %AP_UNWIND
                                        i64 3, label %GLOB_UNWIND
                                        i64 4, label %IND_UNWIND
                                        i64 5, label %CONSTR_UNWIND ]

NUM_UNWIND:
    br label %DONE_UNWIND

AP_UNWIND:
    %pfun = call i64**(i64*)* @getFunPtr(i64* %top)
    %fun = load i64** %pfun
    call void(i64*)* @push(i64* %fun)
    call void()* @unwind()
    br label %DONE_UNWIND

GLOB_UNWIND:
    ; TODO: check for correct number of args, rearrange stack
    %parity = call i64*(i64*)* @getArityPtr(i64* %top)
    %pcode = call void()**(i64*)* @getCodePtr(i64* %top)
    %arity = load i64* %parity
    %code = load void()** %pcode

    ; arguments check

    ; stack rearrangement
    call void(i64)* @rearrange(i64 %arity)

    ; call the function
    call void()* %code()
    br label %DONE_UNWIND

IND_UNWIND:
    call i64*()* @pop()
    %paddr = call i64**(i64*)* @getAddrPtr(i64* %top)
    %addr = load i64** %paddr
    call void(i64*)* @push(i64* %addr)
    call void()* @unwind()
    br label %DONE_UNWIND

CONSTR_UNWIND:
    br label %DONE_UNWIND

otherwise:
    br label %DONE_UNWIND

DONE_UNWIND:
    ret void
}

define void @copyArgsToStack(i64* %pconstr) {
    ; copy constructor arguments to the top of the stack
    %ptop = call i64**()* @getTopPtr()
    %pdest = bitcast i64** %ptop to i8*

    %pargs = call i64**(i64*)* @getConstrArgsPtr(i64* %pconstr)

    %parity = call i64*(i64*)* @getConstrArityPtr(i64* %pconstr)
    %arity = load i64* %parity

    %tmp = sub i64 %arity, 1
    %pargs1 = call i64**(i64, i64**)* @incPtr(i64 %tmp, i64** %pargs)

    ; copying loop
    %pi = alloca i64
    store i64 0, i64* %pi

    %curpsrc = alloca i64**
    store i64** %pargs1, i64*** %curpsrc
    br label %LOOP
LOOP:
    %i = load i64* %pi
    %cond = icmp eq i64 %i, %arity
    br i1 %cond, label %DONE_LOOP, label %COPY
COPY:
    ; copy current argument pointer
    %psrc = load i64*** %curpsrc
    %src = load i64** %psrc
    call void(i64*)* @push(i64* %src)

    ; increment src pointer
    %psrc1 = call i64**(i64, i64**)* @decPtr(i64 1, i64** %psrc)
    store i64** %psrc1, i64*** %curpsrc

    ; increment counter
    %i1 = add i64 1, %i
    store i64 %i1, i64* %pi
    br label %LOOP

DONE_LOOP:
    ret void
}

define void @print() {
    %ptop = call i64**()* @getTopPtr()
    %pret = load i64** %ptop
    %tag = load i64* %pret

    switch i64 %tag, label %ERROR_PRINT [ i64 1, label %NUM_PRINT
                                          i64 5, label %CONSTR_PRINT ]

NUM_PRINT:
    call void(i64*)* @printNum(i64* %pret)
    call i64* @pop()
    br label %DONE_PRINT

CONSTR_PRINT:
    call void(i64*)* @printConstr(i64* %pret)
    br label %DONE_PRINT

ERROR_PRINT:
    %pserr = getelementptr [7 x i8]* @s, i64 0, i64 0
    call i64 (i8 *, ...)* @printf(i8* %pserr)
    %err = add i64 0, 0
    br label %DONE_PRINT

DONE_PRINT:
    ret void
}

define void @printNum(i64* %pret) {
    %psnum = getelementptr [6 x i8]* @snum, i64 0, i64 0
    %pnum = call i64*(i64*)* @getNumPtr(i64* %pret)
    %num = load i64* %pnum
    call i64 (i8 *, ...)* @printf(i8* %psnum, i64 %num)

    ret void
}

define void @printArgs(i64 %arity) {
    %pi = alloca i64
    store i64 0, i64* %pi
    br label %LOOP

LOOP:
    %i = load i64* %pi
    %cond = icmp eq i64 %i, %arity
    br i1 %cond, label %DONE_LOOP, label %EVAL
EVAL:
    call void()* @eval()
    call void()* @print()

    ; increment counter
    %i1 = add i64 %i, 1
    store i64 %i1, i64* %pi
    br label %LOOP

DONE_LOOP:
    ret void
}

define void @printConstr(i64* %pret) {
    ; copy constructor arguments to the top of stack
    call void(i64*)* @copyArgsToStack(i64* %pret)

    %ptag = call i64*(i64*)* @getConstrTagPtr(i64* %pret)
    %tag = load i64* %ptag
    %parity = call i64*(i64*)* @getConstrArityPtr(i64* %pret)
    %arity = load i64* %parity

    %psconstr = getelementptr [13 x i8]* @sconstr, i64 0, i64 0
    call i64 (i8*, ...)* @printf(i8* %psconstr, i64 %tag)

    ; print args
    call void(i64)* @printArgs(i64 %arity)

    ; print right brace
    %psrbr = getelementptr [2 x i8]* @srbr, i64 0, i64 0
    call i64 (i8*, ...)* @printf(i8* %psrbr)

    ret void
}

$constrFuns$

define i64 @main() {
    call void @erl_interface_init()
    store i64 0, i64* @sp
    store i64 0, i64* @vsp
    call void()* @_main()
    call void()* @print()

    ; print new line
    %psnl = getelementptr [2 x i8]* @snl, i64 0, i64 0
    call i64 (i8*, ...)* @printf(i8* %psnl)

    ret i64 0
}

$scs$
