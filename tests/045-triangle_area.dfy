method Main()
  decreases *
{
	{var v := triangle_area(5.0, 3.0); expect v == 7.5, "test 0 failed";}
	{var v := triangle_area(2.0, 2.0); expect v == 2.0, "test 1 failed";}
	{var v := triangle_area(10.0, 8.0); expect v == 40.0, "test 2 failed";}
}