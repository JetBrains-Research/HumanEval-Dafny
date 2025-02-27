method Main()
  decreases *
{
	{var v := has_close_elements([1.0, 2.0, 3.9, 4.0, 5.0, 2.2], 0.3); expect v == true, "test 0 failed";}
	{var v := has_close_elements([1.0, 2.0, 3.9, 4.0, 5.0, 2.2], 0.05); expect v == false, "test 1 failed";}
	{var v := has_close_elements([1.0, 2.0, 5.9, 4.0, 5.0], 0.95); expect v == true, "test 2 failed";}
	{var v := has_close_elements([1.0, 2.0, 5.9, 4.0, 5.0], 0.8); expect v == false, "test 3 failed";}
	{var v := has_close_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.0], 0.1); expect v == true, "test 4 failed";}
	{var v := has_close_elements([1.1, 2.2, 3.1, 4.1, 5.1], 1.0); expect v == true, "test 5 failed";}
	{var v := has_close_elements([1.1, 2.2, 3.1, 4.1, 5.1], 0.5); expect v == false, "test 6 failed";}
}