method Main()
  decreases *
{
	{var v := intersperse([], 7); expect v == [], "test 0 failed";}
	{var v := intersperse([5, 6, 3, 2], 8); expect v == [5, 8, 6, 8, 3, 8, 2], "test 1 failed";}
	{var v := intersperse([2, 2, 2], 2); expect v == [2, 2, 2, 2, 2], "test 2 failed";}
}