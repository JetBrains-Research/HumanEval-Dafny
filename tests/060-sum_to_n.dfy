method Main()
  decreases *
{
	{var v := sum_to_n(1); expect v == 1, "test 0 failed";}
	{var v := sum_to_n(6); expect v == 21, "test 1 failed";}
	{var v := sum_to_n(11); expect v == 66, "test 2 failed";}
	{var v := sum_to_n(30); expect v == 465, "test 3 failed";}
	{var v := sum_to_n(100); expect v == 5050, "test 4 failed";}
}