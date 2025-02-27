method compare(scores: seq<int>, guesses: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |scores| == |guesses|
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |scores|
  ensures forall i :: 0 <= i < |result| ==> result[i] == abs(scores[i] - guesses[i])
  // post-conditions-end
{
  // impl-start
  result := [];
  var i := 0;
  while i < |scores|
    // invariants-start
    invariant 0 <= i <= |scores|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == abs(scores[k] - guesses[k])
    // invariants-end
  {
    result := result + [abs(scores[i] - guesses[i])];
    i := i + 1;
  }
  // impl-end
}

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end
