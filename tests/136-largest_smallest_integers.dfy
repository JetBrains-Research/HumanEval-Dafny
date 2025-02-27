method Main()
  decreases *
{
	{var s, p := largest_smallest_integers([2, 4, 1, 3, 5, 7]); expect [s, p] == [None, Some(1)], "test 0 failed";}
	{var s, p := largest_smallest_integers([2, 4, 1, 3, 5, 7, 0]); expect [s, p] == [None, Some(1)], "test 1 failed";}
	{var s, p := largest_smallest_integers([1, 3, 2, 4, 5, 6, -2]); expect [s, p] == [Some(-2), Some(1)], "test 2 failed";}
	{var s, p := largest_smallest_integers([4, 5, 3, 6, 2, 7, -7]); expect [s, p] == [Some(-7), Some(2)], "test 3 failed";}
	{var s, p := largest_smallest_integers([7, 3, 8, 4, 9, 2, 5, -9]); expect [s, p] == [Some(-9), Some(2)], "test 4 failed";}
	{var s, p := largest_smallest_integers([]); expect [s, p] == [None, None], "test 5 failed";}
	{var s, p := largest_smallest_integers([0]); expect [s, p] == [None, None], "test 6 failed";}
	{var s, p := largest_smallest_integers([-1, -3, -5, -6]); expect [s, p] == [Some(-1), None], "test 7 failed";}
	{var s, p := largest_smallest_integers([-1, -3, -5, -6, 0]); expect [s, p] == [Some(-1), None], "test 8 failed";}
	{var s, p := largest_smallest_integers([-6, -4, -4, -3, 1]); expect [s, p] == [Some(-3), Some(1)], "test 9 failed";}
	{var s, p := largest_smallest_integers([-6, -4, -4, -3, -100, 1]); expect [s, p] == [Some(-3), Some(1)], "test 10 failed";}
}