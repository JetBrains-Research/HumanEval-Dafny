method is_prime(k: int) returns (result: bool)
  requires k >= 2
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
{
  var i := 2;
  result := true;
  while i < k
    invariant 2 <= i <= k
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      result := false;
    }
    i := i + 1;
  }
}

predicate is_prime_pred(k: int) 
{
  forall i :: 2 <= i < k ==> k % i != 0
}

method largest_prime_factor(n: int) returns (largest: int)
  requires n >= 2
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
{
  largest := 1;
  var j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant 1 <= largest < j
    invariant largest == 1 || (largest > 1 && is_prime_pred(largest))
  {
    var flag := is_prime(j);
    if n % j == 0 && flag {
      largest := if largest > j then largest else j;
    }
    j := j + 1;
  }
}

