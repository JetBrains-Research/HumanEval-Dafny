method Main()
  decreases *
{
	{var v := unique([5, 3, 5, 2, 3, 3, 9, 0, 123]); expect v == [0, 2, 3, 5, 9, 123], "test 0 failed";}
}