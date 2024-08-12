predicate IsPrime(n: int)
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

function PrimeLength(s: string): bool
  ensures PrimeLength(s) <==> IsPrime(|s|)
{
  IsPrime(|s|)
}