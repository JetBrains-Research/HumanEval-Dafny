method Main()
  decreases *
{
	{var v := get_row([[1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 1, 6], [1, 2, 3, 4, 5, 1]], 1); expect v == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)], "test 0 failed";}
	{var v := get_row([[1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6]], 2); expect v == [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1)], "test 1 failed";}
	{var v := get_row([[1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [1, 1, 3, 4, 5, 6], [1, 2, 1, 4, 5, 6], [1, 2, 3, 1, 5, 6], [1, 2, 3, 4, 1, 6], [1, 2, 3, 4, 5, 1]], 1); expect v == [(0, 0), (1, 0), (2, 1), (2, 0), (3, 2), (3, 0), (4, 3), (4, 0), (5, 4), (5, 0), (6, 5), (6, 0)], "test 2 failed";}
	{var v := get_row([], 1); expect v == [], "test 3 failed";}
	{var v := get_row([[1]], 2); expect v == [], "test 4 failed";}
	{var v := get_row([[], [1], [1, 2, 3]], 3); expect v == [(2, 2)], "test 5 failed";}
}