method Main()
  decreases *
{
	{var v := f(5); expect v == [1, 2, 6, 24, 15], "test 0 failed";}
	{var v := f(7); expect v == [1, 2, 6, 24, 15, 720, 28], "test 1 failed";}
	{var v := f(1); expect v == [1], "test 2 failed";}
	{var v := f(3); expect v == [1, 2, 6], "test 3 failed";}
}