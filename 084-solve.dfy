method solve(n: nat) returns (r: nat)
  ensures r == popcount(n)
{
  var m := n;
  r := 0;
  while m > 0 
    invariant r + popcount(m) == popcount(n)
  {
    r := r + m % 2;
    m := m / 2;
  }
}

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}