method any_int(a: int, b: int, c: int) returns (r: bool)
  ensures r == (a == b + c || b == a + c || c == a + b)
{
  r := a == b + c || b == a + c || c == a + b;
}