method Main()
  decreases *
{
	{var v := is_equal_to_sum_even(4); expect v == false, "test 0 failed";}
	{var v := is_equal_to_sum_even(6); expect v == false, "test 1 failed";}
	{var v := is_equal_to_sum_even(8); expect v == true, "test 2 failed";}
	{var v := is_equal_to_sum_even(10); expect v == true, "test 3 failed";}
	{var v := is_equal_to_sum_even(11); expect v == false, "test 4 failed";}
	{var v := is_equal_to_sum_even(12); expect v == true, "test 5 failed";}
	{var v := is_equal_to_sum_even(13); expect v == false, "test 6 failed";}
	{var v := is_equal_to_sum_even(16); expect v == true, "test 7 failed";}
}