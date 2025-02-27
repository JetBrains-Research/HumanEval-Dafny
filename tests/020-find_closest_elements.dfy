method Main()
  decreases *
{
	{var s, p := find_closest_elements([1.0, 2.0, 3.9, 4.0, 5.0, 2.2]); expect [s, p] == [3.9, 4.0], "test 0 failed";}
	{var s, p := find_closest_elements([1.0, 2.0, 5.9, 4.0, 5.0]); expect [s, p] == [5.0, 5.9], "test 1 failed";}
	{var s, p := find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.2]); expect [s, p] == [2.0, 2.2], "test 2 failed";}
	{var s, p := find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.0]); expect [s, p] == [2.0, 2.0], "test 3 failed";}
	{var s, p := find_closest_elements([1.1, 2.2, 3.1, 4.1, 5.1]); expect [s, p] == [2.2, 3.1], "test 4 failed";}
}