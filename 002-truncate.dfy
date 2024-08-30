

function truncate(x : real) : (i : real)
    // pre-conditions-start
    requires x >= 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures (0.0 <= x - i < 1.0)
    // post-conditions-end
    {
      // impl-start
        x.Floor as real
      // impl-end
    }
