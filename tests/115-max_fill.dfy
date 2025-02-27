method Main()
  decreases *
{
	{var v := max_fill([[0, 0, 1, 0], [0, 1, 0, 0], [1, 1, 1, 1]], 1); expect v == 6, "test 0 failed";}
	{var v := max_fill([[0, 0, 1, 1], [0, 0, 0, 0], [1, 1, 1, 1], [0, 1, 1, 1]], 2); expect v == 5, "test 1 failed";}
	{var v := max_fill([[0, 0, 0], [0, 0, 0]], 5); expect v == 0, "test 2 failed";}
	{var v := max_fill([[1, 1, 1, 1], [1, 1, 1, 1]], 2); expect v == 4, "test 3 failed";}
	{var v := max_fill([[1, 1, 1, 1], [1, 1, 1, 1]], 9); expect v == 2, "test 4 failed";}
}