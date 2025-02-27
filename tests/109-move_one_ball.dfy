method Main()
  decreases *
{
	{var v := move_one_ball([3, 4, 5, 1, 2]); expect v == true, "test 0 failed";}
	{var v := move_one_ball([3, 5, 10, 1, 2]); expect v == true, "test 1 failed";}
	{var v := move_one_ball([4, 3, 1, 2]); expect v == false, "test 2 failed";}
	{var v := move_one_ball([3, 5, 4, 1, 2]); expect v == false, "test 3 failed";}
	{var v := move_one_ball([]); expect v == true, "test 4 failed";}
}