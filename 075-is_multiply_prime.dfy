predicate is_prime(n: int)
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

method is_multiply_prime(n: int) returns (can: bool)
  requires n >= 2
//   ensures can <==> exists k, l, m :: 2 <= k < n && 2 <= l < n && 2 <= m < n && k * l * m == n
{
    can := false;
    var k := 2;
    while k < n
        invariant k <= n
        // invariant can ==> exists k0, l, m :: 2 <= k0 < k && 2 <= l < n && 2 <= m < n && k0 * l * m == n
    {
        var can_fixed_k := false;

        var l := 2;
        while k * l <= n
            // invariant l <= n + 1
            invariant k * l <= n + k
            invariant can_fixed_k ==> exists l0, m :: 2 <= l0 < l && 2 <= m < n && mul3(k, l0, m) == n
            invariant !can_fixed_k ==> 
                forall l0, m :: 2 <= l0 < l && 2 <= m < n ==> mul3(k, l0, m) != n
        {
            var can_fixed_k_l := false;

            var m := 2;
            while mul3(k, l, m) <= n
                decreases n - mul3(k, l, m)
                invariant m <= n
                invariant mul3(k, l, m) <= n + k * l
                invariant can_fixed_k_l ==> exists m0 :: 2 <= m0 < m && mul3(k, l, m0) == n
                invariant !can_fixed_k_l ==> forall m0 :: 2 <= m0 < m ==> mul3(k, l, m0) != n
            {
                if mul3(k, l, m) == n {
                    can_fixed_k_l := true;
                }
                assert mul3(k, l, m + 1) <= mul3(k, l, m) + k * l <= n + k * l;
                m := m + 1;
            }

            can_fixed_k := can_fixed_k || can_fixed_k_l;

            assert !can_fixed_k_l ==> forall m :: 2 <= m < n && mul3(k, l, m) <= n ==> mul3(k, l, m) != n;
            assert k * (l + 1) <= k * l + k <= n + k;
            assert l + 1 <= n + 1 by {}

            l := l + 1;
        }

        k := k + 1;
        can := can || can_fixed_k;
    }
}

function mul3(a: int, b: int, c: int): int {
    a * b * c
}