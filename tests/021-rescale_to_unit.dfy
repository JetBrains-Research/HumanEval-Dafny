method Main()
  decreases *
{
	{var v := rescale_to_unit([2.0, 49.9]); expect v == [0.0, 1.0], "test 0 failed";}
	{var v := rescale_to_unit([100.0, 49.9]); expect v == [1.0, 0.0], "test 1 failed";}
	{var v := rescale_to_unit([1.0, 2.0, 3.0, 4.0, 5.0]); expect v == [0.0, 0.25, 0.5, 0.75, 1.0], "test 2 failed";}
	{var v := rescale_to_unit([2.0, 1.0, 5.0, 3.0, 4.0]); expect v == [0.25, 0.0, 1.0, 0.5, 0.75], "test 3 failed";}
	{var v := rescale_to_unit([12.0, 11.0, 15.0, 13.0, 14.0]); expect v == [0.25, 0.0, 1.0, 0.5, 0.75], "test 4 failed";}
}