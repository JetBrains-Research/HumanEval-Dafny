method Main()
  decreases *
{
	{var v := pluck([4, 2, 3]); expect v == [2, 1], "test 0 failed";}
	{var v := pluck([1, 2, 3]); expect v == [2, 1], "test 1 failed";}
	{var v := pluck([]); expect v == [], "test 2 failed";}
	{var v := pluck([5, 0, 3, 0, 4, 2]); expect v == [0, 1], "test 3 failed";}
	{var v := pluck([1, 2, 3, 0, 5, 3]); expect v == [0, 3], "test 4 failed";}
	{var v := pluck([5, 4, 8, 4, 8]); expect v == [4, 1], "test 5 failed";}
	{var v := pluck([7, 6, 7, 1]); expect v == [6, 1], "test 6 failed";}
	{var v := pluck([7, 9, 7, 1]); expect v == [], "test 7 failed";}
}