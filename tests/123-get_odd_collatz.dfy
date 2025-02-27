method Main()
  decreases *
{
	{var v := get_odd_collatz(14); expect v == [1, 5, 7, 11, 13, 17], "test 0 failed";}
	{var v := get_odd_collatz(5); expect v == [1, 5], "test 1 failed";}
	{var v := get_odd_collatz(12); expect v == [1, 3, 5], "test 2 failed";}
	{var v := get_odd_collatz(1); expect v == [1], "test 3 failed";}
}