function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

method factorize(n: nat) returns (factors: seq<nat>)
  requires n > 0
  ensures prod(factors) == n
{
  factors := [];
  ghost var taken := 1;
  var cur := n;
  var i := 2;
  while i * i <= cur
    invariant prod(factors) == taken
    invariant taken * cur == n
    invariant cur >= 1
  {
    ghost var pre := cur;
    ghost var temp := 1;
    while cur % i == 0 
      invariant cur >= 1
      invariant temp * cur == pre
      invariant prod(factors) == taken * temp 
      decreases cur - 1
    {
      factors := factors + [i];
      
      cur := cur / i;
      temp := temp * i;
      assert 2 <= i && 2 * cur <= i * cur;
    }
    taken := taken * temp;
    i := i + 1;
  }
  if cur > 1 {
    factors := factors + [cur];
    taken := taken * cur;
  }
  assert taken == n;
}