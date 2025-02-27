method Main()
  decreases *
{
	{var v := multiply(148, 412); expect v == 16, "test 0 failed";}
	{var v := multiply(148, 412); expect v == 16, "test 1 failed";}
	{var v := multiply(19, 28); expect v == 72, "test 2 failed";}
	{var v := multiply(19, 28); expect v == 72, "test 3 failed";}
	{var v := multiply(2020, 1851); expect v == 0, "test 4 failed";}
	{var v := multiply(2020, 1851); expect v == 0, "test 5 failed";}
	{var v := multiply(14, -15); expect v == 20, "test 6 failed";}
	{var v := multiply(14, -15); expect v == 20, "test 7 failed";}
	{var v := multiply(76, 67); expect v == 42, "test 8 failed";}
	{var v := multiply(76, 67); expect v == 42, "test 9 failed";}
	{var v := multiply(17, 27); expect v == 49, "test 10 failed";}
	{var v := multiply(17, 27); expect v == 49, "test 11 failed";}
	{var v := multiply(0, 1); expect v == 0, "test 12 failed";}
	{var v := multiply(0, 1); expect v == 0, "test 13 failed";}
	{var v := multiply(0, 0); expect v == 0, "test 14 failed";}
	{var v := multiply(0, 0); expect v == 0, "test 15 failed";}
}