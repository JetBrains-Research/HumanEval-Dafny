method Main()
  decreases *
{
	{var v := strlen(""); expect v == 0, "test 0 failed";}
	{var v := strlen("x"); expect v == 1, "test 1 failed";}
	{var v := strlen("asdasnakj"); expect v == 9, "test 2 failed";}
}