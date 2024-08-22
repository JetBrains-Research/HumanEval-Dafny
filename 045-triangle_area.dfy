method CalculateTriangleArea(a: real, h: real) returns (area: real)
  requires h >= 0.0 && a >= 0.0
  ensures area == (h * a) / 2.0
{
  area := (h * a) / 2.0;
}
