method Main()
  decreases *
{
	{var v := will_it_fly([3, 2, 3], 9); expect v == true, "test 0 failed";}
	{var v := will_it_fly([1, 2], 5); expect v == false, "test 1 failed";}
	{var v := will_it_fly([3], 5); expect v == true, "test 2 failed";}
	{var v := will_it_fly([3, 2, 3], 1); expect v == false, "test 3 failed";}
	{var v := will_it_fly([1, 2, 3], 6); expect v == false, "test 4 failed";}
	{var v := will_it_fly([5], 5); expect v == true, "test 5 failed";}
}