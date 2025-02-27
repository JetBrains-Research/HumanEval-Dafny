method Main()
  decreases *
{
	{var v := is_sorted([5]); expect v == true, "test 0 failed";}
	{var v := is_sorted([1, 2, 3, 4, 5]); expect v == true, "test 1 failed";}
	{var v := is_sorted([1, 3, 2, 4, 5]); expect v == false, "test 2 failed";}
	{var v := is_sorted([1, 2, 3, 4, 5, 6]); expect v == true, "test 3 failed";}
	{var v := is_sorted([1, 2, 3, 4, 5, 6, 7]); expect v == true, "test 4 failed";}
	{var v := is_sorted([1, 3, 2, 4, 5, 6, 7]); expect v == false, "test 5 failed";}
	{var v := is_sorted([]); expect v == true, "test 6 failed";}
	{var v := is_sorted([1]); expect v == true, "test 7 failed";}
	{var v := is_sorted([3, 2, 1]); expect v == false, "test 8 failed";}
	{var v := is_sorted([1, 2, 2, 2, 3, 4]); expect v == false, "test 9 failed";}
	{var v := is_sorted([1, 2, 3, 3, 3, 4]); expect v == false, "test 10 failed";}
	{var v := is_sorted([1, 2, 2, 3, 3, 4]); expect v == true, "test 11 failed";}
	{var v := is_sorted([1, 2, 3, 4]); expect v == true, "test 12 failed";}
}