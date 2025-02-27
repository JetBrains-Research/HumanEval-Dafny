method Main()
  decreases *
{
	{var v := make_a_pile(3); expect v == [3, 5, 7], "test 0 failed";}
	{var v := make_a_pile(4); expect v == [4, 6, 8, 10], "test 1 failed";}
	{var v := make_a_pile(5); expect v == [5, 7, 9, 11, 13], "test 2 failed";}
	{var v := make_a_pile(6); expect v == [6, 8, 10, 12, 14, 16], "test 3 failed";}
	{var v := make_a_pile(8); expect v == [8, 10, 12, 14, 16, 18, 20, 22], "test 4 failed";}
}