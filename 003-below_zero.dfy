function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

lemma psum_property(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures psum(s[..(i+1)]) == psum(s[..i]) + s[i]
{
    calc == {
        psum(s[..(i+1)]);
        psum(s[..(i+1)][..(i+1)-1]) + s[..(i+1)][(i+1) - 1];
        { assert s[..(i+1)][..(i+1)-1] == s[..i]; }
        psum(s[..i]) + s[i];
    }
}

method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
    {
        // impl-start
        var balance : int := 0;
        var i : int := 0;
        while (i < |ops|)
            // invariants-start
            invariant 0 <= i <= |ops|
            invariant balance == psum(ops[..i])
            invariant forall j : int :: 0 <= j <= i ==> psum(ops[..j]) >= 0
            // invariants-end
        {
            // assert-start
            assert psum(ops[..(i + 1)]) == psum(ops[..i]) + ops[i] by {
                psum_property(ops, i);
            }
            // assert-end
            balance := balance + ops[i];
            if (balance < 0) {
                return false;
            }
            i := i + 1;
        }
        return true;
        // impl-end
    }
