function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else 
        if |a| <= |b| then
            true
        else
            false
}

method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
    sorted := list;
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
    {
        var j := i + 1;
        var min := i;
        while j < |list|
            invariant 0 <= i <= j <= |list|
            invariant 0 <= min < j
        {
            if !comparison(sorted[min], sorted[j], 0) {
                min := j;
            } 
            j := j + 1;
        }
        var temp := sorted[i];
        sorted := sorted[i := sorted[min]][min := temp];
        i := i + 1;
    }
}

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
    sorted := list;
    var i := 0;
    while i < |list|
        invariant 0 <= i <= |list|
        invariant |sorted| == |list|
        invariant multiset(sorted) == multiset(list)
        invariant forall x :: 0 <= x < i ==> forall y :: i <= y < |sorted| ==> |sorted[x]| <= |sorted[y]|
        invariant forall x : int, y : int :: 0 <= x < y < i ==> |sorted[x]| <= |sorted[y]|
        invariant forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    {
        var j := i + 1;
        var min := i;
        while j < |list|
            invariant 0 <= i < j <= |list|
            invariant i <= min < j
            invariant forall x :: i <= x < j ==> |sorted[min]| <= |sorted[x]|
        {
            if |sorted[j]| < |sorted[min]| {
                min := j;
            }
            j := j + 1;
        }
        var temp := sorted[i];
        sorted := sorted[i := sorted[min]][min := temp];
        i := i + 1;
    }
}

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
    var init := sort_strings(list);

    sorted := [];
    var i := 0;

    while i < |init|
        invariant |init| > 0
        invariant multiset(init) == multiset(list)
        invariant 0 <= i <= |init|
        invariant |sorted| <= i
        invariant forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
        invariant multiset(sorted) <= multiset(init[0..i])
    {
        if |init[i]| % 2 == 0 {
            sorted := sorted + [init[i]];
            assert multiset(sorted) <= multiset(init[0..i + 1]);
        } else {
            assert init[0..i + 1] == init[0..i] + [init[i]];
        }
        i := i + 1;
    }
    assert multiset(sorted) <= multiset(init[0..|init|]);
    assert init[0..|init|] == init;

    sorted := sort_lengths(sorted);
}