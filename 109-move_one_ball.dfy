predicate is_sorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method move_one_ball(a: seq<int>) returns (can: bool)
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
{
  if |a| <= 1 {
    assert is_sorted(a[..0]);
    return true;
  }
  can := false;
  var i := 0;
  var min_index := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= min_index < |a|
    invariant forall j :: 0 <= j < i && min_index != j ==> a[min_index] < a[j]
  {
    if a[i] < a[min_index] {
      min_index := i;
    }
    i := i + 1;
  }

  assert forall j :: (
    0 <= j < |a| && min_index != j 
    ==> (
      (forall i :: j <= i < |a| ==> a[j..][i - j] == a[i])
      && (forall i :: 0 <= i < j ==> (a[j..] + a[..j])[|a| - j + i] == a[i])
      && (
        if min_index < j then
          (a[j..] + a[..j])[|a| - j + min_index] == a[min_index]
        else
          (a[j..] + a[..j])[min_index - j] == a[min_index]
      )
      && (
        (exists p :: (
          1 <= p < |a[j..] + a[..j]| 
          && (a[j..] + a[..j])[p] == a[min_index] 
          && (a[j..] + a[..j])[0] > (a[j..] + a[..j])[p]
        )) ==> !is_sorted(a[j..] + a[..j])
      )
    )
  );

  assert forall j :: 0 <= j < |a| && min_index != j ==> !is_sorted(a[j..] + a[..j]);
    
  var new_a := a[min_index..] + a[..min_index];
  can := is_sorted(new_a);
}