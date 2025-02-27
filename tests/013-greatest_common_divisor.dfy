method Main()
  decreases *
{
	{var v := greatest_common_divisor(3, 7); expect v == 1, "test 0 failed";}
	{var v := greatest_common_divisor(10, 15); expect v == 5, "test 1 failed";}
	{var v := greatest_common_divisor(49, 14); expect v == 7, "test 2 failed";}
	{var v := greatest_common_divisor(144, 60); expect v == 12, "test 3 failed";}
}