method Main()
  decreases *
{
	{var v := derivative([3, 1, 2, 4, 5]); expect v == [1, 4, 12, 20], "test 0 failed";}
	{var v := derivative([1, 2, 3]); expect v == [2, 6], "test 1 failed";}
	{var v := derivative([3, 2, 1]); expect v == [2, 2], "test 2 failed";}
	{var v := derivative([3, 2, 1, 0, 4]); expect v == [2, 2, 0, 16], "test 3 failed";}
	{var v := derivative([1]); expect v == [], "test 4 failed";}
}