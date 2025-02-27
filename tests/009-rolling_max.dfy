method Main()
  decreases *
{
	{var v := rolling_max([]); expect v == [], "test 0 failed";}
	{var v := rolling_max([1, 2, 3, 4]); expect v == [1, 2, 3, 4], "test 1 failed";}
	{var v := rolling_max([4, 3, 2, 1]); expect v == [4, 4, 4, 4], "test 2 failed";}
	{var v := rolling_max([3, 2, 3, 100, 3]); expect v == [3, 3, 3, 100, 100], "test 3 failed";}
}