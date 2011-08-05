%ptop = call i64**()* @getTopPtr()
%top = load i64** %ptop
%pnum = call i64*(i64*)* @getNumPtr(i64* %top)
%num = load i64* %pnum

switch i64 %num, label %ALT-1 [ $tags:switchtest(); separator=" "$ ]

$alts$

DEFAULT:
    $defaultCode$
    br label %END_CASE

END_CASE:
