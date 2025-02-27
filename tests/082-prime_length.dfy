method Main()
  decreases *
{
	{var v := prime_length("Hello"); expect v == true, "test 0 failed";}
	{var v := prime_length("abcdcba"); expect v == true, "test 1 failed";}
	{var v := prime_length("kittens"); expect v == true, "test 2 failed";}
	{var v := prime_length("orange"); expect v == false, "test 3 failed";}
	{var v := prime_length("wow"); expect v == true, "test 4 failed";}
	{var v := prime_length("world"); expect v == true, "test 5 failed";}
	{var v := prime_length("MadaM"); expect v == true, "test 6 failed";}
	{var v := prime_length("Wow"); expect v == true, "test 7 failed";}
	{var v := prime_length(""); expect v == false, "test 8 failed";}
	{var v := prime_length("HI"); expect v == true, "test 9 failed";}
	{var v := prime_length("go"); expect v == true, "test 10 failed";}
	{var v := prime_length("gogo"); expect v == false, "test 11 failed";}
	{var v := prime_length("aaaaaaaaaaaaaaa"); expect v == false, "test 12 failed";}
	{var v := prime_length("Madam"); expect v == true, "test 13 failed";}
	{var v := prime_length("M"); expect v == false, "test 14 failed";}
	{var v := prime_length("0"); expect v == false, "test 15 failed";}
}