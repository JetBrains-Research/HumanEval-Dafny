method cube_root(N: nat) returns (r: nat)
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
{
  r := 0;
  while cube(r + 1) <= N
    invariant cube(r) <= N
  {
    r := r + 1;
  }
}

method is_cube(n: nat) returns (r: bool)
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
{
    var root := cube_root(n);
    if cube(root) == n {
        r := true;
    } else {
        cube_of_larger_is_larger();
        r := false;
    }
}

function cube(n: int): int { n * n * n }

lemma cube_of_larger_is_larger()
    ensures forall smaller : int, larger : int :: smaller <= larger ==> cube(smaller) <= cube(larger)
{}