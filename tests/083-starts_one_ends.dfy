method Main()
  decreases *
{
	{var v := starts_one_ends(1); expect v == 1, "test 0 failed";}
	{var v := starts_one_ends(2); expect v == 18, "test 1 failed";}
	{var v := starts_one_ends(3); expect v == 180, "test 2 failed";}
	{var v := starts_one_ends(4); expect v == 1800, "test 3 failed";}
	{var v := starts_one_ends(5); expect v == 18000, "test 4 failed";}
}