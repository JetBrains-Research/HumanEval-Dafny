method Main()
  decreases *
{
	{var v := can_arrange([1, 2, 4, 3, 5]); expect v == 3, "test 0 failed";}
	{var v := can_arrange([1, 2, 4, 5]); expect v == -1, "test 1 failed";}
	{var v := can_arrange([1, 4, 2, 5, 6, 7, 8, 9, 10]); expect v == 2, "test 2 failed";}
	{var v := can_arrange([4, 8, 5, 7, 3]); expect v == 4, "test 3 failed";}
	{var v := can_arrange([]); expect v == -1, "test 4 failed";}
}