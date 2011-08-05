%ptop = call i64**()* @getTopPtr()
%top = load i64** %ptop
%pnum = call i64*(i64*)* @getNumPtr(i64* %top)
%num = load i64* %pnum

switch i64 %num, label %NOT_FOUND [ $tags:switchtest(); separator=" "$ ]

$alts$

NOT_FOUND:
    ret void

END_CASE:
