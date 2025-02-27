method Main()
  decreases *
{
	{var v := compare([1, 2, 3, 4, 5, 1], [1, 2, 3, 4, 2, -2]); expect v == [0, 0, 0, 0, 3, 3], "test 0 failed";}
	{var v := compare([0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]); expect v == [0, 0, 0, 0, 0, 0], "test 1 failed";}
	{var v := compare([1, 2, 3], [-1, -2, -3]); expect v == [2, 4, 6], "test 2 failed";}
	{var v := compare([1, 2, 3, 5], [-1, 2, 3, 4]); expect v == [2, 0, 0, 1], "test 3 failed";}
}