method Main()
  decreases *
{
	{var v := pairs_sum_to_zero([1, 3, 5, 0]); expect v == false, "test 0 failed";}
	{var v := pairs_sum_to_zero([1, 3, -2, 1]); expect v == false, "test 1 failed";}
	{var v := pairs_sum_to_zero([1, 2, 3, 7]); expect v == false, "test 2 failed";}
	{var v := pairs_sum_to_zero([2, 4, -5, 3, 5, 7]); expect v == true, "test 3 failed";}
	{var v := pairs_sum_to_zero([1]); expect v == false, "test 4 failed";}
	{var v := pairs_sum_to_zero([-3, 9, -1, 3, 2, 30]); expect v == true, "test 5 failed";}
	{var v := pairs_sum_to_zero([-3, 9, -1, 3, 2, 31]); expect v == true, "test 6 failed";}
	{var v := pairs_sum_to_zero([-3, 9, -1, 4, 2, 30]); expect v == false, "test 7 failed";}
	{var v := pairs_sum_to_zero([-3, 9, -1, 4, 2, 31]); expect v == false, "test 8 failed";}
}