function sumc(s: seq<int>, p: seq<bool>) : int 
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }

lemma sum_prop(s: seq<int>, p: seq<bool>) 
    requires |s| > 0
    requires |s| == |p|
    ensures sumc(s, p) == sumc(s[..|s| - 1], p[..|s| - 1]) + (if p[ |s| - 1 ] then s[ |s| - 1 ] else 0)
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
        assert (p[1..][..|s[1..]| - 1]) == p[1..|s| - 1];
    }
}

function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
    }

method add(v: seq<int>) returns (r : int)
    ensures r == sumc(v, add_conditon(v))
    {
        r := 0;
        var k := 0;
        var p := add_conditon(v);
        while(k < |v|) 
            invariant 0 <= k <= |v|
            invariant r == sumc(v[..k], p[..k])
        {
            assert v[..k + 1][..k] == v[..k];
            assert p[..k + 1][..k] == p[..k];
            r := r + if p[k] then v[k] else 0;
            k := k + 1;
            assert sumc(v[..k], p[..k]) == r by { sum_prop(v[..k], p[..k]); }
        }
        assert v[..k] == v;
        assert p[..k] == p;
        return r;
    }