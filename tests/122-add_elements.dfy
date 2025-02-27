method Main()
  decreases *
{
	{var v := add_elements([1, -2, -3, 41, 57, 76, 87, 88, 99], 3); expect v == -4, "test 0 failed";}
	{var v := add_elements([111, 121, 3, 4000, 5, 6], 2); expect v == 0, "test 1 failed";}
	{var v := add_elements([11, 21, 3, 90, 5, 6, 7, 8, 9], 4); expect v == 125, "test 2 failed";}
	{var v := add_elements([111, 21, 3, 4000, 5, 6, 7, 8, 9], 4); expect v == 24, "test 3 failed";}
	{var v := add_elements([1], 1); expect v == 1, "test 4 failed";}
}