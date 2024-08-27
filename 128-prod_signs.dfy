function abs(x: int): int 
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}

function sum_abs(s: seq<int>) : int 
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

lemma sum_prop(s: seq<int>) 
  requires |s| > 0
  ensures sum_abs(s) == sum_abs(s[..|s| - 1]) + abs(s[|s| - 1])
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}

method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
{
  s := 0;
  var i := 0;
  while (i < |numbers|)
    invariant 0 <= i <= |numbers|
    invariant s == sum_abs(numbers[..i])
  {
    s := s + abs(numbers[i]);
    assert sum_abs(numbers[..i + 1]) == sum_abs(numbers[..i]) + abs(numbers[i]) by {
      assert numbers[..i+1][..i] == numbers[..i];
      sum_prop(numbers[..i + 1]); 
    }
    i := i + 1;
  }

  assert numbers == numbers[..|numbers|];

  i := 0;
  ghost var negatives := {};
  var cnt := 0;
  while (i < |numbers|)
    invariant 0 <= i <= |numbers|
    invariant cnt == |negatives|
    invariant negatives == set j | 0 <= j < i && numbers[j] < 0
  {
    if (numbers[i] < 0) {
      negatives := negatives + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  assert negatives == set i | 0 <= i < |numbers| && numbers[i] < 0;

  if (cnt % 2 == 1) {
    s := -s;
  }
}

method Main() {
  var nums := [1, 2, 2, -4];
  var s := prod_signs(nums);
  print s;
}