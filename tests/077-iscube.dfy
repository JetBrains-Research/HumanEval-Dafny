method Main()
  decreases *
{
	{var v := iscube(1); expect v == true, "test 0 failed";}
	{var v := iscube(1); expect v == true, "test 1 failed";}
	{var v := iscube(2); expect v == false, "test 2 failed";}
	{var v := iscube(2); expect v == false, "test 3 failed";}
	{var v := iscube(-1); expect v == true, "test 4 failed";}
	{var v := iscube(-1); expect v == true, "test 5 failed";}
	{var v := iscube(64); expect v == true, "test 6 failed";}
	{var v := iscube(64); expect v == true, "test 7 failed";}
	{var v := iscube(180); expect v == false, "test 8 failed";}
	{var v := iscube(180); expect v == false, "test 9 failed";}
	{var v := iscube(1000); expect v == true, "test 10 failed";}
	{var v := iscube(1000); expect v == true, "test 11 failed";}
	{var v := iscube(0); expect v == true, "test 12 failed";}
	{var v := iscube(0); expect v == true, "test 13 failed";}
	{var v := iscube(1729); expect v == false, "test 14 failed";}
	{var v := iscube(1728); expect v == true, "test 15 failed";}
}