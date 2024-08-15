function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (result: nat)
  ensures result == fib(n)
{
  if n == 0 {
    return 0;
  }
  
  if n == 1 {
    return 1;
  }
  
  var a, b := 0, 1;
  var i := 2;
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant a == fib(i - 2)
    invariant b == fib(i - 1)
  {
    var temp := a + b;
    a := b;
    b := temp;
    i := i + 1;
  }
  
  return b;
}