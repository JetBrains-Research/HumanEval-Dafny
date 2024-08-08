function affine(x: real, shift: real, scale: real) : (y : real) 
    requires scale > 0.0
    ensures y == (x + shift) / scale
{
    (x + shift) / scale
}


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
    ensures exists i, j : int :: 0 <= i < |s| && 0 <= j < |s| && r[i] == 0.0 && r[j] == 1.0
    ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
    {
        var mn : real := s[if s[0] < s[1] then 0 else 1];
        var mx : real := s[if s[0] < s[1] then 1 else 0];
        var i : int := 2;
        while (i < |s|) 
            invariant 0 <= i <= |s|
            invariant forall j : int :: (0 <= j < i) ==> mn <= s[j] <= mx
            invariant exists a, b : int :: (0 <= a < i && 0 <= b < i && a != b) && mn == s[a] && mx == s[b]
            invariant mn <= mx
        {
            if (s[i] < mn) {
                mn := s[i];
            }
            if (s[i] > mx) {
                mx := s[i];
            }
            i := i + 1;
        }
        var shift := -mn;
        var scale := mx - mn;
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
        return r;
    }