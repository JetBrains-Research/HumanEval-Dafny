method Main()
  decreases *
{
	{var v := largest_divisor(3); expect v == 1, "test 0 failed";}
	{var v := largest_divisor(7); expect v == 1, "test 1 failed";}
	{var v := largest_divisor(10); expect v == 5, "test 2 failed";}
	{var v := largest_divisor(100); expect v == 50, "test 3 failed";}
	{var v := largest_divisor(49); expect v == 7, "test 4 failed";}
}