method Main()
  decreases *
{
	{var v := is_prime(6); expect v == false, "test 0 failed";}
	{var v := is_prime(101); expect v == true, "test 1 failed";}
	{var v := is_prime(11); expect v == true, "test 2 failed";}
	{var v := is_prime(13441); expect v == true, "test 3 failed";}
	{var v := is_prime(61); expect v == true, "test 4 failed";}
	{var v := is_prime(4); expect v == false, "test 5 failed";}
	{var v := is_prime(1); expect v == false, "test 6 failed";}
	{var v := is_prime(5); expect v == true, "test 7 failed";}
	{var v := is_prime(11); expect v == true, "test 8 failed";}
	{var v := is_prime(17); expect v == true, "test 9 failed";}
	{var v := is_prime(85); expect v == false, "test 10 failed";}
	{var v := is_prime(77); expect v == false, "test 11 failed";}
	{var v := is_prime(255379); expect v == false, "test 12 failed";}
}