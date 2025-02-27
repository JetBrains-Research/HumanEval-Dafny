datatype Option<T> = None | Some(T)


function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}
// pure-end

function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}
// pure-end
lemma sum_prop(s: seq<int>)
  requires |s| > 0
  ensures sum_abs(s) == sum_abs(s[..|s| - 1]) + abs(s[|s| - 1])
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}
// pure-end
method prod_signs(numbers: seq<int>) returns (so: Option<int>)
  ensures so == None <==> |numbers| == 0
  ensures |numbers| > 0 && !(0 in numbers) ==> abs(getVal(so)) == sum_abs(numbers)
  ensures 0 in numbers <==> so == Some(0)
  ensures |numbers| > 0 ==> |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> getVal(so) <= 0
  ensures |numbers| > 0 ==> |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> getVal(so) >= 0
{
  // impl-start
  if |numbers| == 0 {
    return None;
  }
  var s := 0;
  var i := 0;
  while (i < |numbers|)
    // invariants-start
    invariant 0 <= i <= |numbers|
    invariant s == sum_abs(numbers[..i])
    invariant !(0 in numbers[..i])
    // invariants-end
  {
    if numbers[i] == 0 {
        return Some(0);
    }
    s := s + abs(numbers[i]);
    // assert-start
    assert sum_abs(numbers[..i + 1]) == sum_abs(numbers[..i]) + abs(numbers[i]) by {
      assert numbers[..i+1][..i] == numbers[..i];
      sum_prop(numbers[..i + 1]);
    }
    // assert-end
    i := i + 1;
  }

  assert numbers == numbers[..|numbers|]; // assert-line

  i := 0;
  ghost var negatives := {};
  var cnt := 0;
  while (i < |numbers|)
    // invariants-start
    invariant 0 <= i <= |numbers|
    invariant cnt == |negatives|
    invariant negatives == set j | 0 <= j < i && numbers[j] < 0
    // invariants-end
  {
    if (numbers[i] < 0) {
      negatives := negatives + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  assert negatives == set i | 0 <= i < |numbers| && numbers[i] < 0; // assert-line

  if (cnt % 2 == 1) {
    s := -s;
  }
  so := Some(s);
  // impl-end
}