method Main()
  decreases *
{
	{var v := skjkasdkd([0, 3, 2, 1, 3, 5, 7, 4, 5, 5, 5, 2, 181, 32, 4, 32, 3, 2, 32, 324, 4, 3]); expect v == 10, "test 0 failed";}
	{var v := skjkasdkd([1, 0, 1, 8, 2, 4597, 2, 1, 3, 40, 1, 2, 1, 2, 4, 2, 5, 1]); expect v == 25, "test 1 failed";}
	{var v := skjkasdkd([1, 3, 1, 32, 5107, 34, 83278, 109, 163, 23, 2323, 32, 30, 1, 9, 3]); expect v == 13, "test 2 failed";}
	{var v := skjkasdkd([0, 724, 32, 71, 99, 32, 6, 0, 5, 91, 83, 0, 5, 6]); expect v == 11, "test 3 failed";}
	{var v := skjkasdkd([0, 81, 12, 3, 1, 21]); expect v == 3, "test 4 failed";}
	{var v := skjkasdkd([0, 8, 1, 2, 1, 7]); expect v == 7, "test 5 failed";}
	{var v := skjkasdkd([8191]); expect v == 19, "test 6 failed";}
	{var v := skjkasdkd([8191, 123456, 127, 7]); expect v == 19, "test 7 failed";}
	{var v := skjkasdkd([127, 97, 8192]); expect v == 10, "test 8 failed";}
}