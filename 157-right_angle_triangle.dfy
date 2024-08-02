method right_angle_triangle(a : int, b : int, c : int) returns (result : bool)
  ensures result == (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
{
  result := a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a;
}
