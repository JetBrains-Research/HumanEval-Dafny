method make_a_pile(n: int) returns (pile: seq<int>)
  requires n >= 0
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
{
    pile := [];
    if n == 0 {
        return;
    }
    pile := [n];
    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant |pile| == i
        invariant forall j :: 1 <= j < i ==> pile[j] == pile[j - 1] + 2
        invariant n > 0 ==> pile[0] == n
    {
        pile := pile + [pile[i - 1] + 2];
        i := i + 1;
    } 
}