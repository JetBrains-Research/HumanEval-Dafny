method is_equal_to_sum_even(n: int) returns (b : bool)
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
{
  b := n % 2 == 0 && n >= 8;
}
