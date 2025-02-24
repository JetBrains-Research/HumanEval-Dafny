function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// pure-end
lemma power_unit(y: nat)
    ensures power(1, y) == 1
{}
// pure-end
lemma power_monotonic(x: nat, y: nat, j: nat)
    requires x > 0
    requires j >= y
    ensures power(x, j) >= power(x, y)
{}
// pure-end
method is_simple_power(x: int, n: nat) returns (ans : bool)
    // pre-conditions-start
    requires n > 0
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists y :: x == power(n, y)
    // post-conditions-end
{
    // impl-start
    if(n == 1) {
        // assert-start
        assert forall y :: power(n, y) == 1 by { forall y { power_unit(y); } }
        // assert-end
        assert x == 1 ==> x == power(n, 1); // assert-line
        return x == 1;
    }
    var acc := 1;
    var i := 0;
    while(acc < x)
        // invariants-start
        invariant acc == power(n, i)
        invariant forall j : nat :: j < i ==> power(n, j) < x
        // invariants-end
    {
        acc := n * acc;
        i := i + 1;
    }
    if(acc == x) {
        return true;
    } else {
        // assert-start
        assert forall j : nat :: j >= i ==> power(n, j) > x by { forall j | j > i { power_monotonic(n, i, j); } }
        // assert-end
        return false;
    }
    // impl-end
}