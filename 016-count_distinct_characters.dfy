//TODO: General form should accept all characters
function contains_char(s: string, c: char): bool
  decreases |s|
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z' || s[i] == ' '
  requires ('a' <= c <= 'z') || (c == ' ')
{
  if |s| == 0 then false else s[0] == c || (c != ' ' && s[0] == upper_char(c)) || contains_char(s[1..], c)
}
// pure-end
function upper_char(c: char) : (C: char)
  requires 'a' <= c <= 'z'
  ensures 'A' <= C <= 'Z'
{ c - 'a' + 'A' }
// pure-end
method count_distinct_characters(s: string) returns (count: int)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z' || s[i] == ' '
  // pre-conditions-end
  // post-conditions-start
  ensures count == |set c | (('a' <= c <= 'z') || (c == ' ')) && contains_char(s, c)|
  // post-conditions-end
{
  // impl-start
  count := 0;
  ghost var contained: set<char> := {};
  var i := 'a';
  while i <= 'z'
    // invariants-start
    invariant 'a' <= i <= ('z' as int + 1) as char
    invariant count == |contained|
    invariant contained == set c | 'a' <= c < i && contains_char(s, c)
    // invariants-end
  {
    if contains_char(s, i) {
      count := count + 1;
      contained := contained + {i};
    }
    i := (i as int + 1) as char;
  }
  assert contained == set c | 'a' <= c <= 'z' && contains_char(s, c); // assert-line
  if contains_char(s, ' ') {
    count := count + 1;
    contained := contained + {' '};
  }
  assert contained == set c | (('a' <= c <= 'z') || (c == ' ')) && contains_char(s, c); // assert-line
  // impl-end
}