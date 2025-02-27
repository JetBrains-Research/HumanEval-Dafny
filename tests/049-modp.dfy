method Main()
  decreases *
{
	{var v := modp(3, 5); expect v == 3, "test 0 failed";}
	{var v := modp(1101, 101); expect v == 2, "test 1 failed";}
	{var v := modp(0, 101); expect v == 1, "test 2 failed";}
	{var v := modp(3, 11); expect v == 8, "test 3 failed";}
	{var v := modp(100, 101); expect v == 1, "test 4 failed";}
	{var v := modp(30, 5); expect v == 4, "test 5 failed";}
	{var v := modp(31, 5); expect v == 3, "test 6 failed";}
}