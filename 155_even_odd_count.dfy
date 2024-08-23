method even_odd_count(n: nat) returns (even: nat, odd: nat)
  requires n > 0
  ensures even == even_count(n)
  ensures odd == odd_count(n)
{
  var num := n;

  even := 0;
  odd := 0;
  while num > 0
    invariant even + even_count(num) == even_count(n)
    invariant odd + odd_count(num) == odd_count(n)
  {
    even := even + (1 - num % 2);
    odd := odd + num % 2;
    num := num / 10;
  }
}

function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}

function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
