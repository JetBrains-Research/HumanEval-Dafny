function affine(x: real, shift: real, scale: real) : (y : real) 
    requires scale > 0.0
    ensures y == (x + shift) / scale
{
    (x + shift) / scale
}

lemma affine_zero(x: real, shift: real, scale: real)
    requires x == -shift
    requires scale > 0.0
    ensures affine(x, shift, scale) == 0.0 {}

lemma affine_unit(x: real, shift: real, scale: real)
    requires x == scale - shift
    requires scale > 0.0
    ensures affine(x, shift, scale) == 1.0 {}


predicate affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) 
    requires scale > 0.0
    requires |r| == |s|
    {
        forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
    }


lemma div_unit(x: real, scale: real)
    requires 0.0 <= x <= scale
    requires scale > 0.0
    ensures x / scale <= 1.0 {}

method rescale_to_unit(s: seq<real>) returns (r : seq<real>)
    requires |s| >= 2
    requires exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]
    ensures |r| == |s|
    ensures forall i : int :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0
    ensures exists i : int :: 0 <= i < |s| && r[i] == 0.0
    ensures exists i : int :: 0 <= i < |s| && r[i] == 1.0
    ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
    {
        var mni : int := if s[0] < s[1] then 0 else 1;
        var mxi : int := if s[0] < s[1] then 1 else 0;
        var i : int := 2;
        while (i < |s|) 
            invariant 0 <= i <= |s|
            invariant 0 <= mni < |s|
            invariant 0 <= mxi < |s|
            invariant forall j : int :: (0 <= j < i) ==> s[mni] <= s[j] <= s[mxi]
            invariant s[mni] <= s[mxi]
        {
            if (s[i] < s[mni]) {
                mni := i;
            }
            if (s[i] > s[mxi]) {
                mxi := i;
            }
            i := i + 1;
        }
        var shift := -s[mni];
        var scale := s[mxi] - s[mni];
        assert scale > 0.0;
        r := [];
        var j := 0;
        while (j < |s|) 
            invariant 0 <= j <= |s|
            invariant |r| == j
            invariant forall k : int :: 0 <= k < j ==> 0.0 <= r[k] <= 1.0
            invariant affine_seq(s[..j], r, shift, scale)
        {
            var rj : real := s[j] + shift;
            rj := rj / scale;
            assert rj <= 1.0 by { div_unit(s[j] + shift, scale); }
            r := r + [rj];
            j := j + 1;
        }
        assert s[..|s|] == s;
        assert r[mni] == 0.0 by { affine_zero(s[mni], shift, scale); }
        assert r[mxi] == 1.0 by { affine_unit(s[mxi], shift, scale); }
        return r;
    }