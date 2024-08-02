method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
{
  if a < b { m := a; } else { m := b; }
}

method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
{
  if a > b { m := a; } else { m := b; }
}

method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
{
  var left := min(a, b);
  var right := max(a, b);

  var lower := max(2, left);
  var upper := min(8, right);

  result := [];
  var i := lower;
  while i <= upper
    invariant forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
    invariant forall j : int :: j >= 0 && j < |result| ==> result[j] in [2, 4, 6, 8]
  {
    if i % 2 == 0 {
      result := result + [i];
    }
    i := i + 1;
  }
}
