method sort_even_even_length(a: seq<int>) returns (sorted_even: seq<int>)
  requires |a| > 0
  requires |a| % 2 == 0
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted_even| && 2 * j < |sorted_even| ==>
      sorted_even[2 * i] <= sorted_even[2 * j]
  ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
{
  var evens := [];
  var odds := [];
  ghost var all := multiset{};
  ghost var even_multiset := multiset{};
  ghost var odd_multiset := multiset{};

  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |evens| + |odds| == i
    invariant even_multiset == multiset(evens)
    invariant odd_multiset == multiset(odds)
    invariant all == even_multiset + odd_multiset
    invariant all == multiset(a[..i])
    invariant multiset(a[..i]) == multiset(evens) + multiset(odds)
    invariant i % 2 == 0 ==> |evens| == |odds|
    invariant i % 2 == 1 ==> |evens| == |odds| + 1
    invariant forall j :: 0 <= j < |evens| ==> evens[j] == a[2 * j]
    invariant forall j :: 0 <= j < |odds| ==> odds[j] == a[2 * j + 1]
  {
    if i % 2 == 0 {
      evens := evens + [a[i]];
      even_multiset := even_multiset + multiset{a[i]};
    } else {
      odds := odds + [a[i]];
      odd_multiset := odd_multiset + multiset{a[i]};
    }
    all := all + multiset{a[i]};
    assert a[..i] + [a[i]] == a[..i + 1];
    assert multiset(a[..i]) + multiset{a[i]} == multiset(a[..i] + [a[i]]);
    i := i + 1;
  }

  assert |evens| + |odds| == |a|;
  assert a[..|a|] == a;
  assert multiset(a) == multiset(evens) + multiset(odds);

  var seven := SortSeq(evens);

  sorted_even := [];
  assert |seven| == |odds|;
  assert multiset(a) == multiset(seven) + multiset(odds);

  ghost var taken_seven := multiset{};
  ghost var taken_odds := multiset{};
  ghost var all_taken := multiset{};

  var p := 0;
  while p < |odds|
    invariant 0 <= p <= |odds|
    invariant taken_seven == multiset(seven[..p])
    invariant taken_odds == multiset(odds[..p])
    invariant all_taken == taken_seven + taken_odds
    invariant multiset(sorted_even) == all_taken
    invariant |sorted_even| == 2 * p
    invariant forall i :: 0 <= i < p ==> seven[i] == sorted_even[2 * i]
    invariant forall i :: 0 <= i < p ==> odds[i] == sorted_even[2 * i + 1] == a[2 * i + 1]
    invariant forall i :: 0 <= i < |sorted_even| && i % 2 == 1 ==> sorted_even[i] == odds[(i - 1) / 2]
  {
    assert multiset(sorted_even) + multiset{seven[p]} + multiset{odds[p]} 
      == multiset(sorted_even + [seven[p]] + [odds[p]]);

    sorted_even := sorted_even + [seven[p]];
    taken_seven := taken_seven + multiset{seven[p]};

    assert seven[..p] + [seven[p]] == seven[..p + 1];
    assert multiset(seven[..p]) + multiset{seven[p]} == multiset(seven[..p] + [seven[p]]);

    sorted_even := sorted_even + [odds[p]];
    taken_odds := taken_odds + multiset{odds[p]};

    assert odds[..p] + [odds[p]] == odds[..p + 1];
    assert multiset(odds[..p]) + multiset{odds[p]} == multiset(odds[..p] + [odds[p]]); 

    all_taken := all_taken + multiset{seven[p]} + multiset{odds[p]};
    p := p + 1;
  }

  assert seven == seven[..|seven|];
  assert odds == odds[..|odds|];
}

method sorted_even(a: seq<int>) returns (sorted_even: seq<int>)
  requires |a| > 0
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted_even| && 2 * j < |sorted_even| ==>
      sorted_even[2 * i] <= sorted_even[2 * j]
  ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
{
  if |a| == 1 {
    sorted_even := a;
    return;
  }

  if |a| % 2 == 0 {
    sorted_even := sort_even_even_length(a);
    return;
  } 
  if |a| > 1 {
    var m := maxSeq(a);
    var b := a + [m];
    assert |b| == |a| + 1;
    sorted_even := sort_even_even_length(b);

    assert sorted_even[..|sorted_even| - 1] + [sorted_even[|sorted_even| - 1]] == sorted_even[..|sorted_even|];
    assert sorted_even[..|sorted_even|] == sorted_even;
    assert multiset(sorted_even[..|sorted_even| - 1]) 
      == multiset(sorted_even[..|sorted_even|]) - multiset{sorted_even[|sorted_even| - 1]};
    assert multiset(sorted_even[..|sorted_even| - 1]) == multiset(b) - multiset{m};
    assert multiset(sorted_even[..|sorted_even| - 1]) == multiset(a);

    sorted_even := sorted_even[..|sorted_even| - 1];

    return;
  }
}

method maxSeq(a: seq<int>) returns (m: int)
  requires |a| >= 1
  ensures forall k :: 0 <= k < |a| ==> m >= a[k]
  ensures exists k :: 0 <= k < |a| && m == a[k]
{
  m := a[0];
  var index := 1;
  while (index < |a|)
    invariant 0 <= index <= |a|
    invariant forall k :: 0 <= k < index ==> m >= a[k]
    invariant exists k :: 0 <= k < index && m == a[k]
    decreases |a| - index
  {
    m := if m>a[index] then  m else a[index];
    index := index + 1;
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