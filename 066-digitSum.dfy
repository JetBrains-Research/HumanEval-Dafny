function upper_sum_rec(s: string): int
  ensures upper_sum_rec(s) >= 0
{
  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining
}

lemma upper_sum_rec_prop(s: string)
  requires |s| > 0
  ensures upper_sum_rec(s) == upper_sum_rec(s[..|s|-1]) + to_int(s[|s|-1])
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

function to_int(c: char): int 
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}

method upper_sum(s: string) returns (res: int)
    ensures res == upper_sum_rec(s)
{
    res := 0;
    var i := 0;
    while (i < |s|)
        invariant 0 <= i <= |s|
        invariant res == upper_sum_rec(s[..i])
    {
        res := res + to_int(s[i]);
        assert upper_sum_rec(s[..i + 1]) == upper_sum_rec(s[..i]) + to_int(s[i]) by {
            assert s[..i+1][..i] == s[..i];
            upper_sum_rec_prop(s[..i + 1]);
        }
        i := i + 1;
    }
    assert s == s[..|s|];
}   