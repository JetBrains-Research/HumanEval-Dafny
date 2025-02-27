method Main()
  decreases *
{
	{var v := mean_absolute_deviation([1.0, 2.0, 3.0]); expect abs(v - 0.6666667) < 0.00001, "test 0 failed";}
	{var v := mean_absolute_deviation([1.0, 2.0, 3.0, 4.0]); expect abs(v - 1.0) < 0.00001, "test 1 failed";}
	{var v := mean_absolute_deviation([1.0, 2.0, 3.0, 4.0, 5.0]); expect abs(v - 1.2) < 0.00001, "test 2 failed";}
}