method Main()
  decreases *
{
	{var v := x_or_y(7, 34, 12); expect v == 34, "test 0 failed";}
	{var v := x_or_y(15, 8, 5); expect v == 5, "test 1 failed";}
	{var v := x_or_y(3, 33, 5212); expect v == 33, "test 2 failed";}
	{var v := x_or_y(1259, 3, 52); expect v == 3, "test 3 failed";}
	{var v := x_or_y(7919, -1, 12); expect v == -1, "test 4 failed";}
	{var v := x_or_y(3609, 1245, 583); expect v == 583, "test 5 failed";}
	{var v := x_or_y(91, 56, 129); expect v == 129, "test 6 failed";}
	{var v := x_or_y(6, 34, 1234); expect v == 1234, "test 7 failed";}
	{var v := x_or_y(1, 2, 0); expect v == 0, "test 8 failed";}
	{var v := x_or_y(2, 2, 0); expect v == 2, "test 9 failed";}
}