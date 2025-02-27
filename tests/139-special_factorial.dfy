method Main()
  decreases *
{
	{var v := special_factorial(4); expect v == 288, "test 0 failed";}
	{var v := special_factorial(5); expect v == 34560, "test 1 failed";}
	{var v := special_factorial(7); expect v == 125411328000, "test 2 failed";}
	{var v := special_factorial(1); expect v == 1, "test 3 failed";}
}