method Main()
  decreases *
{
	{var v := fib(10); expect v == 55, "test 0 failed";}
	{var v := fib(1); expect v == 1, "test 1 failed";}
	{var v := fib(8); expect v == 21, "test 2 failed";}
	{var v := fib(11); expect v == 89, "test 3 failed";}
	{var v := fib(12); expect v == 144, "test 4 failed";}
}