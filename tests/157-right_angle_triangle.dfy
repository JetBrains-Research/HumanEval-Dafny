method Main()
  decreases *
{
	{var v := right_angle_triangle(3, 4, 5); expect v == true, "test 0 failed";}
	{var v := right_angle_triangle(1, 2, 3); expect v == false, "test 1 failed";}
	{var v := right_angle_triangle(10, 6, 8); expect v == true, "test 2 failed";}
	{var v := right_angle_triangle(2, 2, 2); expect v == false, "test 3 failed";}
	{var v := right_angle_triangle(7, 24, 25); expect v == true, "test 4 failed";}
	{var v := right_angle_triangle(10, 5, 7); expect v == false, "test 5 failed";}
	{var v := right_angle_triangle(5, 12, 13); expect v == true, "test 6 failed";}
	{var v := right_angle_triangle(15, 8, 17); expect v == true, "test 7 failed";}
	{var v := right_angle_triangle(48, 55, 73); expect v == true, "test 8 failed";}
	{var v := right_angle_triangle(1, 1, 1); expect v == false, "test 9 failed";}
	{var v := right_angle_triangle(2, 2, 10); expect v == false, "test 10 failed";}
}