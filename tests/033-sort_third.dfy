method Main()
  decreases *
{
	{var v := sort_third([1, 2, 3]); expect v == [1, 2, 3], "test 0 failed";}
	{var v := sort_third([1, 2, 3]); expect v == [1, 2, 3], "test 1 failed";}
	{var v := sort_third([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]); expect v == [1, 3, -5, 2, -3, 3, 5, 0, 123, 9, -10], "test 2 failed";}
	{var v := sort_third([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]); expect v == [1, 3, -5, 2, -3, 3, 5, 0, 123, 9, -10], "test 3 failed";}
	{var v := sort_third([5, 8, -12, 4, 23, 2, 3, 11, 12, -10]); expect v == [-10, 8, -12, 3, 23, 2, 4, 11, 12, 5], "test 4 failed";}
	{var v := sort_third([5, 8, -12, 4, 23, 2, 3, 11, 12, -10]); expect v == [-10, 8, -12, 3, 23, 2, 4, 11, 12, 5], "test 5 failed";}
	{var v := sort_third([5, 6, 3, 4, 8, 9, 2]); expect v == [2, 6, 3, 4, 8, 9, 5], "test 6 failed";}
	{var v := sort_third([5, 8, 3, 4, 6, 9, 2]); expect v == [2, 8, 3, 4, 6, 9, 5], "test 7 failed";}
	{var v := sort_third([5, 6, 9, 4, 8, 3, 2]); expect v == [2, 6, 9, 4, 8, 3, 5], "test 8 failed";}
	{var v := sort_third([5, 6, 3, 4, 8, 9, 2, 1]); expect v == [2, 6, 3, 4, 8, 9, 5, 1], "test 9 failed";}
}