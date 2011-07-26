declare i32 @printf(i8 *, ...)
declare i8* @malloc(i32)


@s = internal constant [6 x i8] c"ERROR\\00"
@snum = internal constant [4 x i8] c"%d\\0A\\00"
@sp = global i32

define i32 @main() {
    %sp = alloca i32

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
