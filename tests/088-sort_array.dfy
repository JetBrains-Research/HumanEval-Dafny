method Main()
  decreases *
{
	{var v := sort_array([]); expect v == [], "test 0 failed";}
	{var v := sort_array([5]); expect v == [5], "test 1 failed";}
	{var v := sort_array([2, 4, 3, 0, 1, 5]); expect v == [0, 1, 2, 3, 4, 5], "test 2 failed";}
	{var v := sort_array([2, 4, 3, 0, 1, 5, 6]); expect v == [6, 5, 4, 3, 2, 1, 0], "test 3 failed";}
	{var v := sort_array([2, 1]); expect v == [1, 2], "test 4 failed";}
	{var v := sort_array([15, 42, 87, 32, 11, 0]); expect v == [0, 11, 15, 32, 42, 87], "test 5 failed";}
	{var v := sort_array([21, 14, 23, 11]); expect v == [23, 21, 14, 11], "test 6 failed";}
}