
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