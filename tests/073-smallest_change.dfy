method Main()
  decreases *
{
	{var v := smallest_change([1, 2, 3, 5, 4, 7, 9, 6]); expect v == 4, "test 0 failed";}
	{var v := smallest_change([1, 2, 3, 4, 3, 2, 2]); expect v == 1, "test 1 failed";}
	{var v := smallest_change([1, 4, 2]); expect v == 1, "test 2 failed";}
	{var v := smallest_change([1, 4, 4, 2]); expect v == 1, "test 3 failed";}
	{var v := smallest_change([1, 2, 3, 2, 1]); expect v == 0, "test 4 failed";}
	{var v := smallest_change([3, 1, 1, 3]); expect v == 0, "test 5 failed";}
	{var v := smallest_change([1]); expect v == 0, "test 6 failed";}
	{var v := smallest_change([0, 1]); expect v == 1, "test 7 failed";}
}