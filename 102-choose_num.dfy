method choose_num(x : int, y : int) returns (num : int)
  requires 0 <= x && 0 <= y
  ensures num == -1 || (num >= x && num <= y)
  ensures num == -1 || num % 2 == 0
  ensures num == -1 || (forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i)
  ensures num == -1 <==> x >= y
{
  num := -1;
  if x >= y {
    return;
  }
  if x % 2 == 0 {
    num := x;
  } else {
    num := x + 1;
  }
  var i := x + 2;
  while i <= y
    invariant i >= x && i <= y + 1
    invariant num == -1 || num % 2 == 0
    invariant forall j : int :: x <= j < i && j % 2 == 0 ==> num >= j
    invariant num == -1 || (num >= x && num < i)
  {
    if i % 2 == 0 {
      num := i;
    }
    i := i + 1;
  }
}
