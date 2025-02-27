method Main()
  decreases *
{
	{var v := choose_num(12, 15); expect v == 14, "test 0 failed";}
	{var v := choose_num(13, 12); expect v == -1, "test 1 failed";}
	{var v := choose_num(33, 12354); expect v == 12354, "test 2 failed";}
	{var v := choose_num(5234, 5233); expect v == -1, "test 3 failed";}
	{var v := choose_num(6, 29); expect v == 28, "test 4 failed";}
	{var v := choose_num(27, 10); expect v == -1, "test 5 failed";}
	{var v := choose_num(7, 7); expect v == -1, "test 6 failed";}
	{var v := choose_num(546, 546); expect v == 546, "test 7 failed";}
}