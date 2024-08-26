method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
{
  var sum1 := SumChars(list1);
  var sum2 := SumChars(list2);
  
  if sum1 <= sum2 {
    return list1;
  } else {
    return list2;
  }
}

function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

lemma sum_prop(s: seq<string>) 
    requires |s| > 0
    ensures sum_chars_rec(s) == sum_chars_rec(s[..|s| - 1]) + |s[ |s| - 1 ]|
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

method SumChars(list: seq<string>) returns (sum: nat)
  ensures sum == sum_chars_rec(list)
{
    sum := 0;
    var i := 0;
    while (i < |list|)
        invariant 0 <= i <= |list|
        invariant sum == sum_chars_rec(list[..i])
    {
        sum := sum + |list[i]|;
        assert sum_chars_rec(list[..i + 1]) == sum_chars_rec(list[..i]) + |list[i]| by { assert list[..i+1][..i] == list[..i]; sum_prop(list[..i + 1]); }

        i := i + 1;
    }
    assert list == list[..|list|];
}