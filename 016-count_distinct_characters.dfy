function contains_char(s: string, c: char): bool
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  requires 'a' <= c <= 'z'
{
  if |s| == 0 then false else s[0] == c || contains_char(s[1..], c)
}

function upper_char(c: char) : (C: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= C <= 'Z'
{ c - 'a' + 'A' }

method count_distinct_characters(s: string) returns (count: int)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  ensures count == |set c | 'a' <= c <= 'z' && contains_char(s, c)|
{
  count := 0;
  ghost var contained: set<char> := {};
  var i := 'a';
  while i <= 'z'
    invariant 'a' <= i <= ('z' as int + 1) as char
    invariant count == |contained|
    invariant contained == set c | 'a' <= c < i && contains_char(s, c)
  {
    if contains_char(s, i) {
      count := count + 1;
      contained := contained + {i};
    }
    i := (i as int + 1) as char;
  }
  assert contained == set c | 'a' <= c <= 'z' && contains_char(s, c);
}