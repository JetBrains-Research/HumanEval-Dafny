method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
{
  var res: seq<int> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |res| ==> count_rec(a, res[j]) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in res <==> count_rec(a, a[j]) == 1)
    invariant forall j :: 0 <= j < |res| ==> res[j] in a[..i]
  {
    var cnt := count(a, a[i]);
    if cnt == 1 {
      res := res + [a[i]];
    }
    i := i + 1;
  }
  result := res;
}

function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

lemma count_prop(s: seq<int>, x: int)
    requires |s| > 0
    ensures count_rec(s, x) == count_rec(s[..|s| - 1], x) + if s[|s| - 1] == x then 1 else 0
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

method count(a: seq<int>, x: int) returns (cnt: int)
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
{
  cnt := 0;
  ghost var positions: set<int> := {};
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == |positions|
    invariant positions == set k | 0 <= k < i && a[k] == x
    invariant cnt == count_rec(a[..i], x)
  {
    if a[i] == x {
      cnt := cnt + 1;
      positions := positions + {i};
    }
    assert count_rec(a[..i + 1], x) == count_rec(a[..i], x) + (if a[i] == x then 1 else 0) by {
        assert a[..i+1][..i] == a[..i];
        count_prop(a[..i + 1], x);
    }
    i := i + 1;
  }
  assert a == a[..|a|];
}
