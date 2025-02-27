method Main()
  decreases *
{
	{var v := below_threshold([1, 2, 4, 10], 100); expect v == true, "test 0 failed";}
	{var v := below_threshold([1, 20, 4, 10], 5); expect v == false, "test 1 failed";}
	{var v := below_threshold([1, 20, 4, 10], 21); expect v == true, "test 2 failed";}
	{var v := below_threshold([1, 20, 4, 10], 22); expect v == true, "test 3 failed";}
	{var v := below_threshold([1, 8, 4, 10], 11); expect v == true, "test 4 failed";}
	{var v := below_threshold([1, 8, 4, 10], 10); expect v == false, "test 5 failed";}
}