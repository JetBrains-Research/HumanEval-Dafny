method even_odd_count(n: int) returns (even: nat, odd: nat)
  // post-conditions-start
  ensures n == 0 ==> even == 1
  ensures n != 0 ==> even == even_count(abs(n))
  ensures odd == odd_count(abs(n))
  // post-conditions-end
{
  // impl-start
  if n == 0 {
    return 1, 0;
  }
  var num := abs(n);

  even := 0;
  odd := 0;
  while num > 0
    // invariants-start
    invariant even + even_count(num) == even_count(abs(n))
    invariant odd + odd_count(num) == odd_count(abs(n))
    // invariants-end
  {
    even := even + (1 - num % 2);
    odd := odd + num % 2;
    num := num / 10;
  }
  // impl-end
}

function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
// pure-end
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// pure-end

function abs(x: int): nat
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  (if x >= 0 then x else -x) as nat
}
//pure-end