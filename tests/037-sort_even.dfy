method Main()
  decreases *
{
	{var v := sort_even([1, 2, 3]); expect v == [1, 2, 3], "test 0 failed";}
	{var v := sort_even([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]); expect v == [-10, 3, -5, 2, -3, 3, 5, 0, 9, 1, 123], "test 1 failed";}
	{var v := sort_even([5, 8, -12, 4, 23, 2, 3, 11, 12, -10]); expect v == [-12, 8, 3, 4, 5, 2, 12, 11, 23, -10], "test 2 failed";}
}