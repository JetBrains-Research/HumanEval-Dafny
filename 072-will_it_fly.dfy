method will_it_fly(s: seq<int>, w: int) returns (result: bool)
    requires |s| > 0
    ensures result <==> is_palindrome_pred(s) && sum(s) <= w
{
    result := true;
    var i := 0;
    var j := |s| - 1;
    while (i < j)
        invariant 0 <= i < |s|
        invariant 0 <= j < |s|
        invariant j == |s| - i - 1
        invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
    {
        if (s[i] != s[j]) {
            result := false;
            return;
        }
        i := i + 1;
        j := j - 1;
    }

    var total := 0;
    i := 0;
    while (i < |s|)
        invariant 0 <= i <= |s|
        invariant total == sum(s[..i])
    {
        total := total + s[i];
        assert sum(s[..i + 1]) == sum(s[..i]) + s[i] by {
            assert s[..i+1][..i] == s[..i];
            sum_prop(s[..i + 1]);
        }
        i := i + 1;
    }

    assert s[..|s|] == s;
    result := total <= w;
}

predicate is_palindrome_pred(s : seq<int>) {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function sum(s: seq<int>) : int {
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

