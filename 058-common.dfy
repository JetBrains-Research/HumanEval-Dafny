
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>) 
    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
{
    c := {};
    var i := 0;
    while (i < |l1|)
        invariant i >= 0 && i <= |l1|
        invariant forall i :: i in c ==> i in l1 && i in l2
        invariant forall j :: j in l1[..i] && j in l2 ==> j in c
    {
        var j := 0;
        while (j < |l2|)
            invariant j >= 0 && j <= |l2|   
            invariant forall i :: i in c ==> i in l1 && i in l2
            invariant forall k :: ((k in l1[..i] && k in l2) || (k in l1[..i + 1] && k in l2[..j]))==> k in c
        {
            if (l1[i] == l2[j])
            {
                c := c + {l1[i]};
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
