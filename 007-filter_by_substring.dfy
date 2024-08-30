
method checkSubstring(s: string, sub: string) returns (result: bool)
{
    // impl-start
    result := false;
    if (|sub| == 0)
    {
        result := true;
    }
    else if (|s| >= |sub|)
    {
        var i: int := 0;
        while (i <= |s| - |sub|)
        {
            if (s[i..i + |sub|] == sub)
            {
                result := true;
            }
            i := i + 1;
        }
    }
    // impl-end
}

method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)
    // post-conditions-start
    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
    // post-conditions-end
{
    // impl-start
    res := [];
    var i : int := 0;
    while (i < |strings|)
        // invariants-start
        invariant 0 <= i && i <= |strings|
        invariant |res| <= i
        invariant (forall s :: s in res ==> s in strings)
        // invariants-end
    {
        var check : bool := checkSubstring(strings[i], substring);
        if (check)
        {
            res := res + [strings[i]];
        }
        i := i + 1;
    }
    // impl-end
}
