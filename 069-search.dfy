method freq(s: seq<int>, x: int) returns (count: int)
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)| 
{
    count := 0;
    var i := 0;
    ghost var good := {};
    while (i < |s|)
        invariant 0 <= i <= |s|
        invariant count == |good|
        invariant good == (set j | 0 <= j < i && s[j] == x)
    {
        if s[i] == x {
            count := count + 1;
            good := good + {i};
        }
        i := i + 1;
    }
}