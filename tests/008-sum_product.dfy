method Main()
  decreases *
{
	{var s, p := sum_product([]); expect [s, p] == [0, 1], "test 0 failed";}
	{var s, p := sum_product([1, 1, 1]); expect [s, p] == [3, 1], "test 1 failed";}
	{var s, p := sum_product([100, 0]); expect [s, p] == [100, 0], "test 2 failed";}
	{var s, p := sum_product([3, 5, 7]); expect [s, p] == [15, 105], "test 3 failed";}
	{var s, p := sum_product([10]); expect [s, p] == [10, 10], "test 4 failed";}
}