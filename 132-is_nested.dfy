method is_nested(s: string) returns (res: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == '[' || s[i] == ']'
    // pre-conditions-end
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == '[' && s[y] == '[' && s[z] == ']' && s[w] == ']'
    // post-conditions-end
{
    // impl-start
    var bal := 0;
    var i := 0;

    while i < |s| && bal < 2
        // invariants-start
        invariant 0 <= i <= |s|
        invariant (bal >= 1) == (exists x :: 0 <= x < i && s[x] == '[')
        invariant (bal >= 2) == (exists x, y :: 0 <= x < y < i && s[x] == '[' && s[y] == '[')
        invariant !(exists x, y, z :: 0 <= x < y < z < i && s[x] == '[' && s[y] == '[' && s[z] == ']')
        // invariants-end
    {
        if s[i] == '[' {
            bal := bal + 1;
        }
        i := i + 1;
    }

    if bal < 2 {
        return false;
    }

    while i < |s| && bal > 0 
        // invariants-start
        invariant 0 <= i <= |s|
        invariant 0 <= bal <= 2
        invariant exists x, y :: 0 <= x && x < y && y < i && s[x] == '[' && s[y] == '['
        invariant (bal <= 1) == (exists x, y, z :: 0 <= x < y < z < i && s[x] == '[' && s[y] == '[' && s[z] == ']')
        invariant (bal == 0) == (exists x, y, z, w :: 0 <= x < y < z < w < i && s[x] == '[' && s[y] == '[' && s[z] == ']' && s[w] == ']')
        // invariants-end
    {
        if s[i] == ']' {
            bal := bal - 1;
        }
        i := i + 1;
    }

    if bal > 0 {
        return false;
    }

    return true;
    // impl-end
}
