function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
    {
        if a < b then b - a else a - b
    }


// distinct elements
function des(s: seq<real>, a: int, b: int) : bool {
    0 <= a < |s| && 0 <= b < |s| && a != b
}

method find_closest_elements(s: seq<real>) returns (l : real, h : real)
    requires |s| >= 2
    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
    {
        l := s[0];
        h := s[1];
        var d : real := dist(l, h);
        var i : int := 0;
        while (i < |s|) 
            invariant 0 <= i <= |s|
            invariant d == dist(l, h)
            invariant exists a, b :: des(s, a, b) && l == s[a] && h == s[b]
            invariant forall a, b :: a < i && des(s, a, b) ==> d <= dist(s[a], s[b])
        {
            var j : int := i + 1;
            while (j < |s|)
                invariant 0 <= j <= |s|
                invariant d == dist(l, h)
                invariant exists a, b :: des(s, a, b) && l == s[a] && h == s[b]
                invariant forall a, b :: (a < i || (a == i && b < j)) && des(s, a, b) ==> d <= dist(s[a], s[b])
            {
                if dist(s[i], s[j]) <= d {
                    l := s[i];
                    h := s[j];
                    d := dist(l, h);
                }
                j := j + 1;
            }
            i := i + 1;
        }
        if (l <= h) {
            return l, h;
        } else {
            return h, l;
        }
    } 