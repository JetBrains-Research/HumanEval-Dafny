method Main()
  decreases *
{
	{var v := eat(5, 6, 10); expect v == [11, 4], "test 0 failed";}
	{var v := eat(4, 8, 9); expect v == [12, 1], "test 1 failed";}
	{var v := eat(1, 10, 10); expect v == [11, 0], "test 2 failed";}
	{var v := eat(2, 11, 5); expect v == [7, 0], "test 3 failed";}
	{var v := eat(4, 5, 7); expect v == [9, 2], "test 4 failed";}
	{var v := eat(4, 5, 1); expect v == [5, 0], "test 5 failed";}
}