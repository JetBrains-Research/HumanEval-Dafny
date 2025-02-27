method Main()
  decreases *
{
	{var v := sum_squares([1, 2, 3]); expect v == 6, "test 0 failed";}
	{var v := sum_squares([1, 4, 9]); expect v == 14, "test 1 failed";}
	{var v := sum_squares([]); expect v == 0, "test 2 failed";}
	{var v := sum_squares([1, 1, 1, 1, 1, 1, 1, 1, 1]); expect v == 9, "test 3 failed";}
	{var v := sum_squares([-1, -1, -1, -1, -1, -1, -1, -1, -1]); expect v == -3, "test 4 failed";}
	{var v := sum_squares([0]); expect v == 0, "test 5 failed";}
	{var v := sum_squares([-1, -5, 2, -1, -5]); expect v == -126, "test 6 failed";}
	{var v := sum_squares([-56, -99, 1, 0, -2]); expect v == 3030, "test 7 failed";}
	{var v := sum_squares([-1, 0, 0, 0, 0, 0, 0, 0, -1]); expect v == 0, "test 8 failed";}
	{var v := sum_squares([-16, -9, -2, 36, 36, 26, -20, 25, -40, 20, -4, 12, -26, 35, 37]); expect v == -14196, "test 9 failed";}
	{var v := sum_squares([-1, -3, 17, -1, -15, 13, -1, 14, -14, -12, -5, 14, -14, 6, 13, 11, 16, 16, 4, 10]); expect v == -1448, "test 10 failed";}
}