method sum_squares(a : seq<int>) returns (result : seq<int>)
  ensures |result| == |a|
  ensures forall i : int :: i >= 0 && i < |result| && i % 3 == 0 ==> result[i] == a[i] * a[i]
  ensures forall i : int :: i >= 0 && i < |result| && i % 4 == 0 && i % 3 != 0 ==> result[i] == a[i] * a[i] * a[i]
{
  result := [];
  var i := 0;
  while i < |a|
    invariant i >= 0 && i <= |a|
    invariant |result| == i
    invariant forall j : int :: j >= 0 && j < |result| && j % 3 == 0 ==> result[j] == a[j] * a[j]
    invariant forall j : int :: j >= 0 && j < |result| && j % 4 == 0 && j % 3 != 0 ==> result[j] == a[j] * a[j] * a[j]
  {
    if i % 3 == 0 {
      result := result + [a[i] * a[i]];
    } else if i % 4 == 0 && i % 3 != 0 {
      result := result + [a[i] * a[i] * a[i]];
    } else {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
