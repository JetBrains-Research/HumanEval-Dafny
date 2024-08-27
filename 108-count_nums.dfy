method count_nums(s: seq<int>) returns (cnt: nat) 
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
{
  ghost var found := {}; 

  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant found == set j | 0 <= j < i && digits_sum(s[j]) > 0
    invariant cnt == |found|
  {
    if digits_sum(s[i]) > 0 {
      found := found + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}

function abs(x: int): int 
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}