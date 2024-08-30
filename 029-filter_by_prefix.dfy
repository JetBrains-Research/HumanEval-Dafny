method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  // post-conditions-end
{
  // impl-start
  filtered := [];
  var i := 0;
  while i < |xs|
    // invariants-start
    invariant 0 <= i <= |xs|
    invariant forall j :: 0 <= j < |filtered| ==> starts_with(filtered[j], p)
    // invariants-end
  {
    if starts_with(xs[i], p) {
      filtered := filtered + [xs[i]];
    }
    i := i + 1;
  }
  // impl-end
}

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
