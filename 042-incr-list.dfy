
method incr_list(l: seq<int>) returns (result: seq<int>)
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
{
    result := [];
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |result| == i
        invariant forall i1 :: 0 <= i1 < i ==> result[i1] == l[i1] + 1
    {
        result := result + [l[i] + 1];
        i := i + 1;
    }
}