method Main()
  decreases *
{
	{var v := incr_list([]); expect v == [], "test 0 failed";}
	{var v := incr_list([3, 2, 1]); expect v == [4, 3, 2], "test 1 failed";}
	{var v := incr_list([5, 2, 5, 2, 3, 3, 9, 0, 123]); expect v == [6, 3, 6, 3, 4, 4, 10, 1, 124], "test 2 failed";}
}