method Main()
  decreases *
{
	{var v := factorize(2); expect v == [2], "test 0 failed";}
	{var v := factorize(4); expect v == [2, 2], "test 1 failed";}
	{var v := factorize(8); expect v == [2, 2, 2], "test 2 failed";}
	{var v := factorize(57); expect v == [3, 19], "test 3 failed";}
	{var v := factorize(3249); expect v == [3, 3, 19, 19], "test 4 failed";}
	{var v := factorize(185193); expect v == [3, 3, 3, 19, 19, 19], "test 5 failed";}
	{var v := factorize(20577); expect v == [3, 19, 19, 19], "test 6 failed";}
	{var v := factorize(18); expect v == [2, 3, 3], "test 7 failed";}
}