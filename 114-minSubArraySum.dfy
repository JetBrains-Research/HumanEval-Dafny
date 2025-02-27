function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}
// pure-end
method minSubArraySum(a: seq<int>) returns (s: int)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall p,q :: 0 <= p < q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k < m <= |a| && s == Sum(a, k, m)
  // post-conditions-end
{
  // impl-start
  var k, m := 0, 1;
  s := a[0];
  var n := 1;
  var c, t := 0, a[0];
  while n < |a|
    // invariants-start
    invariant 0 <= c < n <= |a| && t == Sum(a, c, n)
    invariant forall b :: 0 <= b < n ==> Sum(a, b, n) >= Sum(a, c, n)
    invariant 0 <= k < m <= n && s == Sum(a, k, m)
    invariant forall p,q :: 0 <= p < q <= n ==> Sum(a, p, q) >= Sum(a, k, m)
    // invariants-end
  {
    t, n := t + a[n], n + 1;
    if t > a[n - 1] {
      c, t := n - 1, a[n - 1];
    }
    if s > t {
      k, m, s := c, n, t;
    }
  }
  // impl-end
}
