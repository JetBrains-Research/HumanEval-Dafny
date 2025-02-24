method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures (k > 1 && !result) ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  // impl-start
  if k == 1 {
    result := false;
    return;
  }
  result := true;
  for i := 2 to k
    // invariants-start
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
    // invariants-end
  {
    if k % i == 0 {
      result := false;
      return;
    }
  }
  // impl-end
}
