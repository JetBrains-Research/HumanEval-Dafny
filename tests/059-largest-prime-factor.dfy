method Main()
  decreases *
{
	{var v := largest_prime_factor(15); expect v == 5, "test 0 failed";}
	{var v := largest_prime_factor(27); expect v == 3, "test 1 failed";}
	{var v := largest_prime_factor(63); expect v == 7, "test 2 failed";}
	{var v := largest_prime_factor(330); expect v == 11, "test 3 failed";}
	{var v := largest_prime_factor(13195); expect v == 29, "test 4 failed";}
}