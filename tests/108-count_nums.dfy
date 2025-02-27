method Main()
  decreases *
{
	{var v := count_nums([]); expect v == 0, "test 0 failed";}
	{var v := count_nums([-1, -2, 0]); expect v == 0, "test 1 failed";}
	{var v := count_nums([1, 1, 2, -2, 3, 4, 5]); expect v == 6, "test 2 failed";}
	{var v := count_nums([1, 6, 9, -6, 0, 1, 5]); expect v == 5, "test 3 failed";}
	{var v := count_nums([1, 100, 98, -7, 1, -1]); expect v == 4, "test 4 failed";}
	{var v := count_nums([12, 23, 34, -45, -56, 0]); expect v == 5, "test 5 failed";}
	{var v := count_nums([0, 1]); expect v == 1, "test 6 failed";}
	{var v := count_nums([1]); expect v == 1, "test 7 failed";}
}