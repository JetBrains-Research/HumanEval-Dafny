predicate Prime(p: nat)
    {
        p > 1 &&
        forall k :: 1 < k < p ==> p % k != 0
    }

method is_multiply_prime(x: nat) returns (ans : bool)
    requires x > 1
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    {
        for a := 2 to x 
            invariant forall i: nat, j: nat, k: nat :: (Prime(i) && Prime(j) && Prime(k) && i < a) ==> x != i * j * k
        {
            if Prime(a) {
                for b := 2 to x 
                    invariant forall j: nat, k: nat :: (Prime(j) && Prime(k) && j < b) ==> x != a * j * k
                {
                    if Prime(b) {
                        for c := 2 to x 
                            invariant forall k: nat :: (Prime(k) && k < c) ==> x != a * b * k
                        {
                            if Prime(c) && x == a * b * c {
                                    return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }