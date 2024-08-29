predicate IsPrime(n: int)
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

function PrimeLength(s: string): bool
  // post-conditions-start
  ensures PrimeLength(s) <==> IsPrime(|s|)
  // post-conditions-end
{
  // impl-start
  IsPrime(|s|)
  // impl-end
}
