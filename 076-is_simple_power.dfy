function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

lemma power_unit(y: nat)
    ensures power(1, y) == 1 
{}

lemma power_monotonic(x: nat, y: nat, j: nat)
    requires x > 0
    requires j >= y
    ensures power(x, j) >= power(x, y)
{}

method is_simple_power(x: nat, n: int) returns (ans : bool)
    requires x > 0
    ensures ans <==> exists y :: n == power(x, y)
    {
        if(x == 1) {
            assert forall y :: power(x, y) == 1  by { forall y { power_unit(y); } }
            assert n == 1 ==> n == power(x, 1);
            return n == 1;
        }
        var acc := 1;
        var i := 0;
        while(acc < n)
            invariant acc == power(x, i)
            invariant forall j : nat :: j < i ==> power(x, j) < n
        {
            acc := x * acc;
            i := i + 1;
        }
        if(acc == n) {
            return true;
        } else {
            assert forall j : nat :: j >= i ==> power(x, j) > n by { forall j | j > i { power_monotonic(x, i, j); } }
            return false;
        }
    }