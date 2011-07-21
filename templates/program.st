declare i32 @printf(i8 *, ...)
declare i8* @malloc(i32)
@s = internal constant [6 x i8] c"ERROR\\00"
@resstr = internal constant [4 x i8] c"%d\\0A\\00"

define i32 @main() {
    %pres = call i32* ()* @_main()
    %res = load i32* %pres
    %ps = getelementptr [4 x i8]* @resstr, i64 0, i64 0
    call i32 (i8 *, ...)* @printf(i8* %ps, i32 %res)
    ret i32 0
}

$scs$
