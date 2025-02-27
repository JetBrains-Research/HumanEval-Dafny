method Main()
  decreases *
{
	{var v := below_zero([]); expect v == false, "test 0 failed";}
	{var v := below_zero([1, 2, -3, 1, 2, -3]); expect v == false, "test 1 failed";}
	{var v := below_zero([1, 2, -4, 5, 6]); expect v == true, "test 2 failed";}
	{var v := below_zero([1, -1, 2, -2, 5, -5, 4, -4]); expect v == false, "test 3 failed";}
	{var v := below_zero([1, -1, 2, -2, 5, -5, 4, -5]); expect v == true, "test 4 failed";}
	{var v := below_zero([1, -2, 2, -2, 5, -5, 4, -4]); expect v == true, "test 5 failed";}
}