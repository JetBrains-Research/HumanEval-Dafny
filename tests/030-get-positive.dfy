method Main()
  decreases *
{
	{var v := get_positive([-1, -2, 4, 5, 6]); expect v == [4, 5, 6], "test 0 failed";}
	{var v := get_positive([5, 3, -5, 2, 3, 3, 9, 0, 123, 1, -10]); expect v == [5, 3, 2, 3, 3, 9, 123, 1], "test 1 failed";}
	{var v := get_positive([-1, -2]); expect v == [], "test 2 failed";}
	{var v := get_positive([]); expect v == [], "test 3 failed";}
}