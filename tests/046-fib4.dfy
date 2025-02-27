method Main()
  decreases *
{
	{var v := fib4(5); expect v == 4, "test 0 failed";}
	{var v := fib4(8); expect v == 28, "test 1 failed";}
	{var v := fib4(10); expect v == 104, "test 2 failed";}
	{var v := fib4(12); expect v == 386, "test 3 failed";}
}