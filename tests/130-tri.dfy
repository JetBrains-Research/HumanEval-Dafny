method Main()
  decreases *
{
	{var v := tri(3); expect v == [1, 3, 2, 8], "test 0 failed";}
	{var v := tri(4); expect v == [1, 3, 2, 8, 3], "test 1 failed";}
	{var v := tri(5); expect v == [1, 3, 2, 8, 3, 15], "test 2 failed";}
	{var v := tri(6); expect v == [1, 3, 2, 8, 3, 15, 4], "test 3 failed";}
	{var v := tri(7); expect v == [1, 3, 2, 8, 3, 15, 4, 24], "test 4 failed";}
	{var v := tri(8); expect v == [1, 3, 2, 8, 3, 15, 4, 24, 5], "test 5 failed";}
	{var v := tri(9); expect v == [1, 3, 2, 8, 3, 15, 4, 24, 5, 35], "test 6 failed";}
	{var v := tri(20); expect v == [1, 3, 2, 8, 3, 15, 4, 24, 5, 35, 6, 48, 7, 63, 8, 80, 9, 99, 10, 120, 11], "test 7 failed";}
	{var v := tri(0); expect v == [1], "test 8 failed";}
	{var v := tri(1); expect v == [1, 3], "test 9 failed";}
}