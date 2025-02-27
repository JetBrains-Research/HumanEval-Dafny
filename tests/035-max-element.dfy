method Main()
  decreases *
{
	{var v := max_element([1, 2, 3]); expect v == 3, "test 0 failed";}
	{var v := max_element([5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]); expect v == 124, "test 1 failed";}
}