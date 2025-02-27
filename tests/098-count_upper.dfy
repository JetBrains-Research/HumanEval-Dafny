method Main()
  decreases *
{
	{var v := count_upper("aBCdEf"); expect v == 1, "test 0 failed";}
	{var v := count_upper("abcdefg"); expect v == 0, "test 1 failed";}
	{var v := count_upper("dBBE"); expect v == 0, "test 2 failed";}
	{var v := count_upper("B"); expect v == 0, "test 3 failed";}
	{var v := count_upper("U"); expect v == 1, "test 4 failed";}
	{var v := count_upper(""); expect v == 0, "test 5 failed";}
	{var v := count_upper("EEEE"); expect v == 2, "test 6 failed";}
}