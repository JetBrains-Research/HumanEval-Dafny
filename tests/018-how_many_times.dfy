method Main()
  decreases *
{
	{var v := how_many_times("", "x"); expect v == 0, "test 0 failed";}
	{var v := how_many_times("xyxyxyx", "x"); expect v == 4, "test 1 failed";}
	{var v := how_many_times("cacacacac", "cac"); expect v == 4, "test 2 failed";}
	{var v := how_many_times("john doe", "john"); expect v == 1, "test 3 failed";}
}