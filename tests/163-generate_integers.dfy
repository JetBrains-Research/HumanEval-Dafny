method Main()
  decreases *
{
	{var v := generate_integers(2, 10); expect v == [2, 4, 6, 8], "test 0 failed";}
	{var v := generate_integers(10, 2); expect v == [2, 4, 6, 8], "test 1 failed";}
	{var v := generate_integers(132, 2); expect v == [2, 4, 6, 8], "test 2 failed";}
	{var v := generate_integers(17, 89); expect v == [], "test 3 failed";}
}