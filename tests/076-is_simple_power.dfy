method Main()
  decreases *
{
	{var v := is_simple_power(16, 2); expect v == true, "test 0 failed";}
	{var v := is_simple_power(143214, 16); expect v == false, "test 1 failed";}
	{var v := is_simple_power(4, 2); expect v == true, "test 2 failed";}
	{var v := is_simple_power(9, 3); expect v == true, "test 3 failed";}
	{var v := is_simple_power(16, 4); expect v == true, "test 4 failed";}
	{var v := is_simple_power(24, 2); expect v == false, "test 5 failed";}
	{var v := is_simple_power(128, 4); expect v == false, "test 6 failed";}
	{var v := is_simple_power(12, 6); expect v == false, "test 7 failed";}
	{var v := is_simple_power(1, 1); expect v == true, "test 8 failed";}
	{var v := is_simple_power(1, 12); expect v == true, "test 9 failed";}
}