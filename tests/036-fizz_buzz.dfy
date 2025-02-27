method Main()
  decreases *
{
	{var v := fizz_buzz(50); expect v == 0, "test 0 failed";}
	{var v := fizz_buzz(78); expect v == 2, "test 1 failed";}
	{var v := fizz_buzz(79); expect v == 3, "test 2 failed";}
	{var v := fizz_buzz(100); expect v == 3, "test 3 failed";}
	{var v := fizz_buzz(200); expect v == 6, "test 4 failed";}
	{var v := fizz_buzz(4000); expect v == 192, "test 5 failed";}
	{var v := fizz_buzz(10000); expect v == 639, "test 6 failed";}
	{var v := fizz_buzz(100000); expect v == 8026, "test 7 failed";}
}