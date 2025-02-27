method Main()
  decreases *
{
	{var v := circular_shift(100, 2); expect v == "001", "test 0 failed";}
	{var v := circular_shift(12, 2); expect v == "12", "test 1 failed";}
	{var v := circular_shift(97, 8); expect v == "79", "test 2 failed";}
	{var v := circular_shift(12, 1); expect v == "21", "test 3 failed";}
	{var v := circular_shift(11, 101); expect v == "11", "test 4 failed";}
}