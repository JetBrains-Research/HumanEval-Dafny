function sum(s: seq<int>) : int
    {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }

lemma sum_prop(s: seq<int>) 
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

function number_seq(n: int) : (r : seq<int>) 
        requires n >= 0
        ensures |r| == n
    {
        seq(n, i => i + 1)
    }

method sum_squares(n: int) returns (r : int)
    requires n >= 1
    ensures r == sum(number_seq(n))
    {
        r := 0;
        var k := 0;
        ghost var v := number_seq(n);
        while(k < n) 
            invariant 0 <= k <= |v|
            invariant r == sum(v[..k])
        {
            assert v[..k + 1][..k] == v[..k];
            r := r + (k + 1);
            k := k + 1;
            assert sum(v[..k]) == r by { sum_prop(v[..k]); }
        }
        assert v[..k] == v;
        return r;
    }