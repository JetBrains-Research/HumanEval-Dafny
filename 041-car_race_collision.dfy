method car_race_collision(n: int) returns (cnt: int)
  requires n >= 0
  ensures cnt == n * n
{
  cnt := n * n;
}
