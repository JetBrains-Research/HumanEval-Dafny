method Compare(scores: array<int>, guesses: array<int>) returns (result: array<int>)
  requires scores.Length == guesses.Length
  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> 
    result[i] == if scores[i] == guesses[i] then 0 else abs(scores[i] - guesses[i])
{
  result := new int[scores.Length];
  var i := 0;
  while i < scores.Length
    invariant 0 <= i <= scores.Length
    invariant result.Length == scores.Length
    invariant forall k :: 0 <= k < i ==> 
      result[k] == if scores[k] == guesses[k] then 0 else abs(scores[k] - guesses[k])
  {
    if scores[i] == guesses[i] {
      result[i] := 0;
    } else {
      result[i] := abs(scores[i] - guesses[i]);
    }
    i := i + 1;
  }
}

function abs(x: int): int
{
  if x < 0 then -x else x
}