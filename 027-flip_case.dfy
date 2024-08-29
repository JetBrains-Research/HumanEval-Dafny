predicate lower(c: char)
    {
        'a' <= c <= 'z'
    }

predicate upper(c: char)
    {
        'A' <= c <= 'Z'
    }
predicate alpha(c: char)
    {
        lower(c) || upper(c)
    }

function flip_char(c: char) : (C: char)
        ensures lower(c) <==> upper(C)
        ensures upper(c) <==> lower(C)
    {
        if lower(c) then c - 'a' + 'A' else
        if upper(c) then c + 'a' - 'A' else c
    }

    function flip_case(s: string) : (S: string)
        // post-conditions-start
        ensures |S| == |s|
        ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
        ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
        // post-conditions-end
        {
        // impl-start
            seq(|s|, i requires 0 <= i < |s| => flip_char(s[i]))
        // impl-end
        }
