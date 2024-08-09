predicate IsPrime(n: int)
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

method CountUpTo(n: int) returns (primes: seq<int>)
  requires n >= 0
  ensures forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  ensures forall i :: 0 <= i < |primes| ==> primes[i] < n
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
{
  primes := [];
  if n <= 2 { return; }
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
    invariant forall j :: 0 <= j < |primes| ==> 2 <= primes[j] < i
    invariant forall p :: 2 <= p < i && IsPrime(p) <==> p in primes
    invariant forall j, k :: 0 <= j < k < |primes| ==> primes[j] < primes[k]
  {
    if IsPrime(i) {
      primes := primes + [i];
    }
    i := i + 1;
  }
}