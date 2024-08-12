
method get_positive(l : seq<int>) returns (result : seq<int>)
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 : int :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
{
    result := [];
    var i : int := 0;
    while i < |l|
        invariant i >= 0 && i <= |l|
        invariant |result| <= i
        invariant forall i1 : int :: i1 >= 0 && i1 < |result| ==> result[i1] > 0
        invariant i > 0 ==> (l[i - 1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i - 1])
        invariant forall i1 : int :: i1 >= 0 && i1 < old(|result|) ==> old(result[i1]) == result[i1]
        invariant forall i1 :: i1 >= 0 && i1 < i ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
        invariant |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 : int :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]));
    {
        var n : int := l[i];
        if n > 0 {
            ghost var res_prev := result;
            assert forall i1 :: i1 >= 0 && i1 < i ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1]);
            result := result + [n];
            assert result[|result| - 1] == n;
            assert forall i1 :: i1 >= 0 && i1 < |res_prev| ==> res_prev[i1] == result[i1];
            assert forall i1 :: i1 >= 0 && i1 < i ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |res_prev| && res_prev[i2] == l[i1]);
        }
        i := i + 1;
    }
}  