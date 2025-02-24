function digitSum_rec(s: string): int
  // post-conditions-start
  ensures digitSum_rec(s) >= 0
  // post-conditions-end
{
  // impl-start
  if |s| == 0 then
    0
  else
    var remaining := digitSum_rec(s[1..]);
    to_int(s[0]) + remaining
  // impl-end
}

lemma digitSum_rec_prop(s: string)
  requires |s| > 0
  ensures digitSum_rec(s) == digitSum_rec(s[..|s|-1]) + to_int(s[|s|-1])
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}
// pure-end
method digitSum(s: string) returns (res: int)
    // post-conditions-start
    ensures res == digitSum_rec(s)
    // post-conditions-end
{
    // impl-start
    res := 0;
    var i := 0;
    while (i < |s|)
        // invariants-start
        invariant 0 <= i <= |s|
        invariant res == digitSum_rec(s[..i])
        // invariants-end
    {
        res := res + to_int(s[i]);
        // assert-start
        assert digitSum_rec(s[..i + 1]) == digitSum_rec(s[..i]) + to_int(s[i]) by {
            assert s[..i+1][..i] == s[..i];
            digitSum_rec_prop(s[..i + 1]);
        }
        // assert-end
        i := i + 1;
    }
    assert s == s[..|s|]; // assert-line
    // impl-end
}
