

function truncate(x : real) : (i : real)
    requires x >= 0.0
    ensures (0.0 <= x - i < 1.0)
    {
        x.Floor as real
    }