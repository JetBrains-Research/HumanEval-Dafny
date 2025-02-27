method Main()
  decreases *
{
	{var v := maximum([-3, -4, 5], 3); expect v == [-4, -3, 5], "test 0 failed";}
	{var v := maximum([4, -4, 4], 2); expect v == [4, 4], "test 1 failed";}
	{var v := maximum([-3, 2, 1, 2, -1, -2, 1], 1); expect v == [2], "test 2 failed";}
	{var v := maximum([123, -123, 20, 0, 1, 2, -3], 3); expect v == [2, 20, 123], "test 3 failed";}
	{var v := maximum([-123, 20, 0, 1, 2, -3], 4); expect v == [0, 1, 2, 20], "test 4 failed";}
	{var v := maximum([5, 15, 0, 3, -13, -8, 0], 7); expect v == [-13, -8, 0, 0, 3, 5, 15], "test 5 failed";}
	{var v := maximum([-1, 0, 2, 5, 3, -10], 2); expect v == [3, 5], "test 6 failed";}
	{var v := maximum([1, 0, 5, -7], 1); expect v == [5], "test 7 failed";}
	{var v := maximum([4, -4], 2); expect v == [-4, 4], "test 8 failed";}
	{var v := maximum([-10, 10], 2); expect v == [-10, 10], "test 9 failed";}
	{var v := maximum([1, 2, 3, -23, 243, -400, 0], 0); expect v == [], "test 10 failed";}
}