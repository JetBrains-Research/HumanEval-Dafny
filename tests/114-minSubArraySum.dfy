method Main()
  decreases *
{
	{var v := minSubArraySum([2, 3, 4, 1, 2, 4]); expect v == 1, "test 0 failed";}
	{var v := minSubArraySum([-1, -2, -3]); expect v == -6, "test 1 failed";}
	{var v := minSubArraySum([-1, -2, -3, 2, -10]); expect v == -14, "test 2 failed";}
	{var v := minSubArraySum([-9999999999999999]); expect v == -9999999999999999, "test 3 failed";}
	{var v := minSubArraySum([0, 10, 20, 1000000]); expect v == 0, "test 4 failed";}
	{var v := minSubArraySum([-1, -2, -3, 10, -5]); expect v == -6, "test 5 failed";}
	{var v := minSubArraySum([100, -1, -2, -3, 10, -5]); expect v == -6, "test 6 failed";}
	{var v := minSubArraySum([10, 11, 13, 8, 3, 4]); expect v == 3, "test 7 failed";}
	{var v := minSubArraySum([100, -33, 32, -1, 0, -2]); expect v == -33, "test 8 failed";}
	{var v := minSubArraySum([-10]); expect v == -10, "test 9 failed";}
	{var v := minSubArraySum([7]); expect v == 7, "test 10 failed";}
	{var v := minSubArraySum([1, -1]); expect v == -1, "test 11 failed";}
}