method skjkasdkd(lst: seq<nat>) returns (dsum: nat)
  requires exists i :: 0 <= i < |lst| && is_prime(lst[i])
  ensures dsum == digits_sum(max_seq(filter_primes(lst)))
{
  var primes := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant primes == filter_primes(lst[..i])
  {
    if is_prime(lst[i]) {
      primes := primes + [lst[i]];
    }
    assert filter_primes(lst[..i + 1]) == filter_primes(lst[..i]) + (
      if is_prime(lst[i]) then [lst[i]] else []
    ) by {
      assert lst[..i+1][..i] == lst[..i];
      primes_prop(lst[..i + 1]); 
    }
    i := i + 1;
  }

  assert lst[..|lst|] == lst;

  var max_prime := primes[0];
  i := 1;
  while i < |primes|
    invariant 1 <= i <= |primes|
    invariant forall j :: 0 <= j < i ==> max_prime >= primes[j]
    invariant max_prime == max_seq(primes[..i]);
  {
    max_prime := max(max_prime, primes[i]);
    assert max_seq(primes[..i + 1]) == max(max_seq(primes[..i]), primes[i]) by {
      assert primes[..i + 1][..i] == primes[..i];
      max_prop(primes[..i + 1]);
    }
    i := i + 1;
  }

  assert primes[..|primes|] == primes;
  assert max_prime == max_seq(primes);

  dsum := digits_sum(max_prime);
}

function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}

function max_seq(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
{
  if |lst| == 1 
    then lst[0] 
    else 
      var suf := max_seq(lst[1..]);
      max(lst[0], suf)
}

lemma max_prop(s: seq<int>) 
  requires |s| > 1
  ensures max_seq(s) == max(max_seq(s[..|s| - 1]), s[|s| - 1])
{
  assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
}

function filter_primes(lst: seq<int>): (primes: seq<int>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0 
    then [] 
    else 
      var tail := filter_primes(lst[1..]);
      (if is_prime(lst[0]) then [lst[0]] else []) + tail
}

lemma primes_prop(s: seq<int>) 
    requires |s| > 0
    ensures filter_primes(s) == filter_primes(s[..|s| - 1]) + (
      if is_prime(s[|s| - 1]) then [s[|s| - 1]] else []
    )
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

function max(a: int, b: int): int
  ensures max(a, b) == a || max(a, b) == b
  ensures max(a, b) >= a && max(a, b) >= b
{
  if a > b then a else b
}

predicate is_prime(k: int) {
  k != 1 && forall i :: 2 <= i < k ==> k % i != 0
}