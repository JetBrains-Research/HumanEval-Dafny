method Main()
  decreases *
{
	{var v := car_race_collision(2); expect v == 4, "test 0 failed";}
	{var v := car_race_collision(3); expect v == 9, "test 1 failed";}
	{var v := car_race_collision(4); expect v == 16, "test 2 failed";}
	{var v := car_race_collision(8); expect v == 64, "test 3 failed";}
	{var v := car_race_collision(10); expect v == 100, "test 4 failed";}
}