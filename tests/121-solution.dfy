method Main()
  decreases *
{
	{var v := solution([5, 8, 7, 1]); expect v == 12, "test 0 failed";}
	{var v := solution([3, 3, 3, 3, 3]); expect v == 9, "test 1 failed";}
	{var v := solution([30, 13, 24, 321]); expect v == 0, "test 2 failed";}
	{var v := solution([5, 9]); expect v == 5, "test 3 failed";}
	{var v := solution([2, 4, 8]); expect v == 0, "test 4 failed";}
	{var v := solution([30, 13, 23, 32]); expect v == 23, "test 5 failed";}
	{var v := solution([3, 13, 2, 9]); expect v == 3, "test 6 failed";}
}