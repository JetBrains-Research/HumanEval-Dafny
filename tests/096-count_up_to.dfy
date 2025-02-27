method Main()
  decreases *
{
	{var v := count_up_to(5); expect v == [2, 3], "test 0 failed";}
	{var v := count_up_to(6); expect v == [2, 3, 5], "test 1 failed";}
	{var v := count_up_to(7); expect v == [2, 3, 5], "test 2 failed";}
	{var v := count_up_to(10); expect v == [2, 3, 5, 7], "test 3 failed";}
	{var v := count_up_to(0); expect v == [], "test 4 failed";}
	{var v := count_up_to(22); expect v == [2, 3, 5, 7, 11, 13, 17, 19], "test 5 failed";}
	{var v := count_up_to(1); expect v == [], "test 6 failed";}
	{var v := count_up_to(18); expect v == [2, 3, 5, 7, 11, 13, 17], "test 7 failed";}
	{var v := count_up_to(47); expect v == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43], "test 8 failed";}
	{var v := count_up_to(101); expect v == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97], "test 9 failed";}
}