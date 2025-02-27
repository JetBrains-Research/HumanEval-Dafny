method Main()
  decreases *
{
	{var v := sum_squares([1.0, 2.0, 3.0]); expect v == 14, "test 0 failed";}
	{var v := sum_squares([1.0, 2.0, 3.0]); expect v == 14, "test 1 failed";}
	{var v := sum_squares([1.0, 3.0, 5.0, 7.0]); expect v == 84, "test 2 failed";}
	{var v := sum_squares([1.4, 4.2, 0.0]); expect v == 29, "test 3 failed";}
	{var v := sum_squares([-2.4, 1.0, 1.0]); expect v == 6, "test 4 failed";}
	{var v := sum_squares([100.0, 1.0, 15.0, 2.0]); expect v == 10230, "test 5 failed";}
	{var v := sum_squares([10000.0, 10000.0]); expect v == 200000000, "test 6 failed";}
	{var v := sum_squares([-1.4, 4.6, 6.3]); expect v == 75, "test 7 failed";}
	{var v := sum_squares([-1.4, 17.9, 18.9, 19.9]); expect v == 1086, "test 8 failed";}
	{var v := sum_squares([0.0]); expect v == 0, "test 9 failed";}
	{var v := sum_squares([-1.0]); expect v == 1, "test 10 failed";}
	{var v := sum_squares([-1.0, 1.0, 0.0]); expect v == 2, "test 11 failed";}
}