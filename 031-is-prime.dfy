method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  // impl-start
  var i := 2;
  result := true;
  while i < k
    // invariants-start
    invariant 2 <= i <= k
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
    // invariants-end
  {
    if k % i == 0 {
      result := false;
    }
    i := i + 1;
  }
  // impl-end
}
