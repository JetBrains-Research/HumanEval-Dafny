method derivative(xs: seq<int>) returns (result: seq<int>)
  requires |xs| > 0
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
{
  result := [];
  var i := 1;
  while i < |xs|
    invariant 1 <= i <= |xs|
    invariant |result| == i - 1
    invariant forall j :: 0 <= j < |result| ==> result[j] == xs[j+1] * (j+1)
  {
    result := result + [xs[i] * i];
    i := i + 1;
  }
}