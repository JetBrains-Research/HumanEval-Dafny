function tri_rec(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri_rec(n - 1) + tri_rec(n - 2) + tri_rec(n + 1)
}
// pure-end
method tri(n: nat) returns (result: seq<nat>)
  // post-conditions-start
  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri_rec(i)
  // post-conditions-end
{
  // impl-start
  if n == 0 {
    result := [1];
  } else {
    result := [1, 3];
    var i := 2;
    while i <= n
      // invariants-start
      invariant 0 <= i <= n + 1
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == tri_rec(j)
      // invariants-end
    {
      if i % 2 == 0 {
        result := result + [1 + i / 2];
      } else {
        assert result[i - 2] == tri_rec(i - 2); // assert-line
        assert result[i - 1] == tri_rec(i - 1); // assert-line
        assert (i + 3) / 2 == tri_rec(i + 1); // assert-line
        result := result + [result[i - 2] + result[i - 1] + (i + 3) / 2];
      }
      i := i + 1;
    }
  }
  // impl-end
}
