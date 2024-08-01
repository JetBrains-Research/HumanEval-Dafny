
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
{
    b := true;
    var i : int := 0;
    while (i < |l|)
        invariant 0 <= i && i <= |l|
        invariant b == (forall i1 : int :: i1 >= 0 && i1 < i ==> l[i1] < t)
    {
        if (l[i] >= t)
        {
            b := false;
        }
        i := i + 1;
    }
}
