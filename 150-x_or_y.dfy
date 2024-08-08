predicate IsPrime(n: nat)
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

method x_or_y(n: nat, x: int, y: int) returns (result: int)
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
{
  if IsPrime(n) {
    return x;
  } else {
    return y;
  }
}