method Main()
  decreases *
{
	{var v := is_multiply_prime(5); expect v == false, "test 0 failed";}
	{var v := is_multiply_prime(30); expect v == true, "test 1 failed";}
	{var v := is_multiply_prime(8); expect v == true, "test 2 failed";}
	{var v := is_multiply_prime(10); expect v == false, "test 3 failed";}
}