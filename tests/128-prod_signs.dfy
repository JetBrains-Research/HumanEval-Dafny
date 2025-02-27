method Main()
  decreases *
{
	{var v := prod_signs([1, 2, 2, -4]); expect v == Some(-9), "test 0 failed";}
	{var v := prod_signs([0, 1]); expect v == Some(0), "test 1 failed";}
	{var v := prod_signs([1, 1, 1, 2, 3, -1, 1]); expect v == Some(-10), "test 2 failed";}
	{var v := prod_signs([]); expect v == None, "test 3 failed";}
	{var v := prod_signs([2, 4, 1, 2, -1, -1, 9]); expect v == Some(20), "test 4 failed";}
	{var v := prod_signs([-1, 1, -1, 1]); expect v == Some(4), "test 5 failed";}
	{var v := prod_signs([-1, 1, 1, 1]); expect v == Some(-4), "test 6 failed";}
	{var v := prod_signs([-1, 1, 1, 0]); expect v == Some(0), "test 7 failed";}
}