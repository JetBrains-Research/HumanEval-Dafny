method Main()
  decreases *
{
	{var v := exchange([1, 2, 3, 4], [1, 2, 3, 4]); expect v == "YES", "test 0 failed";}
	{var v := exchange([1, 2, 3, 4], [1, 5, 3, 4]); expect v == "NO", "test 1 failed";}
	{var v := exchange([1, 2, 3, 4], [2, 1, 4, 3]); expect v == "YES", "test 2 failed";}
	{var v := exchange([5, 7, 3], [2, 6, 4]); expect v == "YES", "test 3 failed";}
	{var v := exchange([5, 7, 3], [2, 6, 3]); expect v == "NO", "test 4 failed";}
	{var v := exchange([3, 2, 6, 1, 8, 9], [3, 5, 5, 1, 1, 1]); expect v == "NO", "test 5 failed";}
	{var v := exchange([100, 200], [200, 200]); expect v == "YES", "test 6 failed";}
}