method Main()
  decreases *
{
	{var v := monotonic([1, 2, 4, 10]); expect v == true, "test 0 failed";}
	{var v := monotonic([1, 2, 4, 20]); expect v == true, "test 1 failed";}
	{var v := monotonic([1, 20, 4, 10]); expect v == false, "test 2 failed";}
	{var v := monotonic([4, 1, 0, -10]); expect v == true, "test 3 failed";}
	{var v := monotonic([4, 1, 1, 0]); expect v == true, "test 4 failed";}
	{var v := monotonic([1, 2, 3, 2, 5, 60]); expect v == false, "test 5 failed";}
	{var v := monotonic([1, 2, 3, 4, 5, 60]); expect v == true, "test 6 failed";}
	{var v := monotonic([9, 9, 9, 9]); expect v == true, "test 7 failed";}
}