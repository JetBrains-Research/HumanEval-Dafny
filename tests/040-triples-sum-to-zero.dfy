method Main()
  decreases *
{
	{var v := triples_sum_to_zero([1, 3, 5, 0]); expect v == false, "test 0 failed";}
	{var v := triples_sum_to_zero([1, 3, 5, -1]); expect v == false, "test 1 failed";}
	{var v := triples_sum_to_zero([1, 3, -2, 1]); expect v == true, "test 2 failed";}
	{var v := triples_sum_to_zero([1, 2, 3, 7]); expect v == false, "test 3 failed";}
	{var v := triples_sum_to_zero([1, 2, 5, 7]); expect v == false, "test 4 failed";}
	{var v := triples_sum_to_zero([2, 4, -5, 3, 9, 7]); expect v == true, "test 5 failed";}
	{var v := triples_sum_to_zero([1]); expect v == false, "test 6 failed";}
	{var v := triples_sum_to_zero([1, 3, 5, -100]); expect v == false, "test 7 failed";}
	{var v := triples_sum_to_zero([100, 3, 5, -100]); expect v == false, "test 8 failed";}
}