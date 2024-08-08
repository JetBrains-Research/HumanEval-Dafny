


method largest_divisor(n: int) returns (d : int)
    requires n > 1
    ensures 1 <= d < n
    ensures n % d == 0
    ensures forall k :: d < k < n ==> n % k != 0
    {
        d := n - 1;
        while (d >= 1)
            invariant 1 <= d < n
            invariant forall k :: d < k < n ==> n % k != 0
        {
            if (n % d == 0) {
                return d;
            }
            d := d - 1;
        }
        return 1;
    }