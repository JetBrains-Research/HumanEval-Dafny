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

function ceil(f: real) : (c : int)
    {
        (f + 1.0).Floor
    }

function square_seq(lst: seq<real>) : (sq : seq<int>) 
        ensures |sq| == |lst|
    {
        seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]))
    }

method sum_squares(lst: seq<real>) returns (r : int)
    ensures r == sum(square_seq(lst))
    {
        r := 0;
        var k := 0;
        var v := square_seq(lst);
        while(k < |lst|) 
            invariant 0 <= k <= |lst|
            invariant r == sum(v[..k])
        {
            assert v[..k + 1][..k] == v[..k];
            r := r + v[k];
            k := k + 1;
            assert sum(v[..k]) == r by { sum_prop(v[..k]); }
        }
        assert v[..k] == v;
        return r;
    }