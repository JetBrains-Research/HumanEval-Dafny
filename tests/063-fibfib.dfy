method Main()
  decreases *
{
	{var v := fibfib(2); expect v == 1, "test 0 failed";}
	{var v := fibfib(1); expect v == 0, "test 1 failed";}
	{var v := fibfib(5); expect v == 4, "test 2 failed";}
	{var v := fibfib(8); expect v == 24, "test 3 failed";}
	{var v := fibfib(10); expect v == 81, "test 4 failed";}
	{var v := fibfib(12); expect v == 274, "test 5 failed";}
	{var v := fibfib(14); expect v == 927, "test 6 failed";}
}