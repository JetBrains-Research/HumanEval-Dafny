method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
    result := [];
    var i := 0;
    while (i < |s|)
        invariant 0 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
        invariant forall k :: 0 <= k < |result| ==> exists m :: 0 <= m < i && result[k] == s[m]
        invariant forall j :: 0 <= j < i ==> s[j] in result
    {
        if |result| == 0 || result[|result| - 1] != s[i] {
            assert |result| == 0 || result[|result| - 1] < s[i];
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method unique(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
    var sorted := SortSeq(s);
    result := uniqueSorted(sorted);
    assert forall x :: x in sorted ==> x in s by {
        assert forall x :: x in multiset(sorted) ==> x in s;
    }
    assert forall x :: x in s ==> x in sorted by {
        assert forall x :: x in multiset(s) ==> x in sorted;
    }
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
}