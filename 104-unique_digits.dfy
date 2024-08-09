predicate HasNoEvenDigit(n: int)
  decreases n
{
  n >= 0 && (n < 10 || (n % 10 % 2 != 0 && HasNoEvenDigit(n / 10)))
}

method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
{
  result := [];
  
  for i := 0 to |x|
    invariant forall j :: 0 <= j < |result| ==> HasNoEvenDigit(result[j])
    invariant forall e :: e in result ==> e in x[..i]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in result
  {
    if HasNoEvenDigit(x[i]) {
      result := result + [x[i]];
    }
  }

  ghost var unsorted := result;
  
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
    invariant multiset(unsorted) == multiset(result)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |result| ==> result[j] <= result[k]
    invariant forall e :: e in result ==> HasNoEvenDigit(e)
    invariant forall e :: e in result ==> e in x
  {
    var minIndex := i;
    var j := i + 1;
    while j < |result|
      invariant i <= minIndex < j <= |result|
      invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
    {
      if result[j] < result[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := result[i];
      result := result[i := result[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }

  assert forall e :: e in result ==> HasNoEvenDigit(e);
  assert forall e :: e in result ==> e in x;
  assert forall e :: e in x && HasNoEvenDigit(e) ==> e in result by {
    assert forall e :: e in unsorted ==> e in multiset(result);
  }
}