method CountNumbersStartingOrEndingWithOne(n: nat) returns (count: nat)
    requires n > 0
    ensures n == 1 ==> count == 1
    ensures n > 1 ==> count == 18 * Pow(10, n - 2)
{
    if n == 1 {
        count := 1;
    } else {
        count := 18 * Pow(10, n - 2);
    }
}

function Pow(base: nat, exponent: nat): nat
    ensures exponent == 0 ==> Pow(base, exponent) == 1
    ensures exponent > 0 ==> Pow(base, exponent) == base * Pow(base, exponent-1)
{
    if exponent == 0 then 1 else base * Pow(base, exponent-1)
}