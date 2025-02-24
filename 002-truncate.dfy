

method truncate_number(x : real) returns (d : real)
    // pre-conditions-start
    requires x >= 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures (0.0 <= d <= 1.0)
    ensures (x - d) == (x.Floor as real)
    // post-conditions-end
    {
      // impl-start
      return x - (x.Floor as real);
      // impl-end
    }
