declare %struct._eterm* @erl_mk_pid(i8*, i32, i32, i8 zeroext)

declare i8* @erl_thisnodename()

declare signext i16 @erl_thiscreation()

declare %struct._eterm* @erl_mk_atom(i8*)

declare %struct._eterm* @erl_mk_tuple(%struct._eterm**, i32)

declare i8* @llvm.stacksave() nounwind

declare i32 @sleep(i32)

declare i32 @erl_reg_send(i32, i8*, %struct._eterm*)

declare i32 @erl_receive_msg(i32, i8*, i32, %struct.ErlMessage*)

declare i32 @erl_connect(i8*)

declare void @erl_err_quit(i8*, ...) noreturn


%struct.ErlMessage = type { i32, %struct._eterm*, %struct._eterm*, %struct._eterm*, [256 x i8] }
%struct.Erl_Atom = type { %struct.Erl_Header, i32, i8* }
%struct.Erl_Big = type { %struct.Erl_Header, i32, i32, i16* }
%struct.Erl_Binary = type { %struct.Erl_Header, i32, i8* }
%struct.Erl_EmptyList = type { %struct.Erl_Header }
%struct.Erl_Float = type { %struct.Erl_Header, double }
%struct.Erl_Function = type { %struct.Erl_Header, i32, i32, [16 x i8], i32, %struct._eterm*, %struct._eterm*, %struct._eterm*, %struct._eterm*, %struct._eterm** }
%struct.Erl_Header = type { [3 x i8], i8 }
%struct.Erl_Integer = type { %struct.Erl_Header, i32 }
%struct.Erl_LLInteger = type { %struct.Erl_Header, i64 }
%struct.Erl_List = type { %struct.Erl_Header, %struct._eterm*, %struct._eterm* }
%struct.Erl_Pid = type { %struct.Erl_Header, i8*, i32, i32, i8 }
%struct.Erl_Port = type { %struct.Erl_Header, i8*, i32, i8 }
%struct.Erl_Ref = type { %struct.Erl_Header, i8*, i32, [3 x i32], i8 }
%struct.Erl_Tuple = type { %struct.Erl_Header, i32, %struct._eterm** }
%struct.Erl_ULLInteger = type { %struct.Erl_Header, i64 }
%struct.Erl_Uinteger = type { %struct.Erl_Header, i32 }
%struct.Erl_Variable = type { %struct.Erl_Header, i32, i8*, %struct._eterm* }
%struct._eterm = type { %union.anon }
%union.anon = type { %struct.Erl_Function }

@BUF_SIZE = constant i32 1024, align 4
@.str = private unnamed_addr constant [14 x i8] c"pong@kurvinox\\00"
@.str1 = private unnamed_addr constant [26 x i8] c"ERROR: erl_connect failed\\00"
@.str2 = private unnamed_addr constant [5 x i8] c"ping\\00"
@.str3 = private unnamed_addr constant [5 x i8] c"pong\\00"
@.str4 = private unnamed_addr constant [20 x i8] c"Ping received pong\\0A\\00"
@.str5 = private unnamed_addr constant [7 x i8] c"secret\\00"
@.str6 = private unnamed_addr constant [31 x i8] c"ERROR: erl_connect_init failed\\00"

define void @_connect() nounwind {
    %sockfd = alloca i32, align 4
    %nodename = alloca i8*, align 8
    store i8* getelementptr inbounds ([14 x i8]* @.str, i32 0, i32 0), i8** %nodename, align 8
    %1 = load i8** %nodename, align 8
    %2 = call i32 @erl_connect(i8* %1)
    store i32 %2, i32* %sockfd, align 4
    %3 = icmp slt i32 %2, 0
    br i1 %3, label %4, label %5

; <label>:4                                       ; preds = %0
    call void (i8*, ...)* @erl_err_quit(i8* getelementptr inbounds ([26 x i8]* @.str1, i32 0, i32 0)) noreturn
    unreachable

; <label>:5                                       ; preds = %0
    %6 = load i32* %sockfd, align 4
    %7 = sext i32 %6 to i64

    ; push socket to the stack
    %tag = call i64*(i64)* @hAllocNum(i64 %7)
    call void(i64*)* @push(i64* %tag)

    $update(ninstr="0"; n="0")$
    $unwind()$

    ret void
}

define void @_send() nounwind {
    $push(ninstr="0"; n="0")$

    $eval()$

    %top = call i64**()* @getTopPtr()
    %addr = load i64** %top

    %numptr = call i64*(i64*)* @getNumPtr(i64* %addr)
    %num = load i64* %numptr

    %sockfd = trunc i64 %num to i32

    %1 = alloca i32, align 4
    %arr = alloca [2 x %struct._eterm*], align 16
    %ping_msg = alloca %struct._eterm*, align 8
    %2 = alloca i8*
    %emsg = alloca %struct.ErlMessage, align 8
    store i32 %sockfd, i32* %1, align 4
    %3 = call i8* @erl_thisnodename()
    %4 = load i32* %1, align 4
    %5 = call signext i16 @erl_thiscreation()
    %6 = trunc i16 %5 to i8
    %7 = call %struct._eterm* @erl_mk_pid(i8* %3, i32 %4, i32 0, i8 zeroext %6)
    %8 = getelementptr inbounds [2 x %struct._eterm*]* %arr, i32 0, i64 0
    store %struct._eterm* %7, %struct._eterm** %8
    %9 = call %struct._eterm* @erl_mk_atom(i8* getelementptr inbounds ([5 x i8]* @.str2, i32 0, i32 0))
    %10 = getelementptr inbounds [2 x %struct._eterm*]* %arr, i32 0, i64 1
    store %struct._eterm* %9, %struct._eterm** %10
    %11 = getelementptr inbounds [2 x %struct._eterm*]* %arr, i32 0, i32 0
    %12 = call %struct._eterm* @erl_mk_tuple(%struct._eterm** %11, i32 2)
    store %struct._eterm* %12, %struct._eterm** %ping_msg, align 8
    %13 = call i8* @llvm.stacksave()
    store i8* %13, i8** %2
    %14 = alloca i8, i64 1024, align 16
    br label %15

; <label>:15                                      ; preds = %26, %0
    br label %16

; <label>:16                                      ; preds = %15
    %17 = call i32 @sleep(i32 1)
    %18 = load i32* %1, align 4
    %19 = load %struct._eterm** %ping_msg, align 8
    %20 = call i32 @erl_reg_send(i32 %18, i8* getelementptr inbounds ([5 x i8]* @.str3, i32 0, i32 0), %struct._eterm* %19)
    %21 = load i32* %1, align 4
    %22 = call i32 @erl_receive_msg(i32 %21, i8* %14, i32 1024, %struct.ErlMessage* %emsg)
    %23 = icmp eq i32 %22, 1
    br i1 %23, label %24, label %26

; <label>:24                                      ; preds = %16
    %25 = call i64 (i8*, ...)* @printf(i8* getelementptr inbounds ([20 x i8]* @.str4, i32 0, i32 0))
    br label %26

; <label>:26                                      ; preds = %24, %16
    br label %15
                                                  ; No predecessors!

    $update(ninstr="1"; n="0")$
    $pop(ninstr="2"; n="0")$
    $unwind()$

    ret void
}

define void @erl_interface_init() nounwind {
  %identification_number = alloca i32, align 4
  %creation = alloca i32, align 4
  %cookie = alloca i8*, align 8
  call void @erl_init(i8* null, i64 0)
  store i32 99, i32* %identification_number, align 4
  store i32 1, i32* %creation, align 4
  store i8* getelementptr inbounds ([7 x i8]* @.str5, i32 0, i32 0), i8** %cookie, align 8
  %1 = load i32* %identification_number, align 4
  %2 = load i8** %cookie, align 8
  %3 = load i32* %creation, align 4
  %4 = trunc i32 %3 to i16
  %5 = call i32 @erl_connect_init(i32 %1, i8* %2, i16 signext %4)
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %8, label %7

; <label>:7                                       ; preds = %0
  call void (i8*, ...)* @erl_err_quit(i8* getelementptr inbounds ([31 x i8]* @.str6, i32 0, i32 0)) noreturn
  unreachable

; <label>:8                                       ; preds = %0
  ret void
}

declare void @erl_init(i8*, i64)

declare i32 @erl_connect_init(i32, i8*, i16 signext)

