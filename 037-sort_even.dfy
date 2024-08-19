method sorted_even(a: seq<int>) returns (sorted_even: seq<int>)
  requires |a| > 0
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted_even| && 2 * j < |sorted_even| ==>
      sorted_even[2 * i] <= sorted_even[2 * j]
  ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
{
  var p := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |p| == i
    invariant forall j :: 0 <= j < i ==> p[j] == (j % 2 == 0)
  {
    p := p + [i % 2 == 0];
    i := i + 1;
  }

  sorted_even := SortSeqPred(a, p);
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  requires |s| == |p|
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant forall j, k :: 0 <= j < k < i && p[j] && p[k] ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i && p[j] ==> forall k :: i <= k < |sorted| && p[k] ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
  {
    if p[i] {
      var minIndex := i;
      var j := i + 1;
      while j < |sorted|
        invariant i <= minIndex < j <= |sorted|
        invariant p[minIndex]
        invariant forall k :: i <= k < j && p[k] ==> sorted[minIndex] <= sorted[k]
      {
        if p[j] && sorted[j] < sorted[minIndex] {
          minIndex := j;
        }
        j := j + 1;
      }
      if minIndex != i {
        var temp := sorted[i];
        sorted := sorted[i := sorted[minIndex]][minIndex := temp];
      }
    }
    i := i + 1;
  }
}