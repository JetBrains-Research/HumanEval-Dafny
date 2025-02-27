method Main()
  decreases *
{
	{var v := truncate_number(3.5); expect v == 0.5, "test 0 failed";}
	{var v := truncate_number(1.33); expect v == 0.33, "test 1 failed";}
	{var v := truncate_number(123.456); expect v == 0.456, "test 2 failed";}
}