method Main()
  decreases *
{
	{var v := add([4, 88]); expect v == 88, "test 0 failed";}
	{var v := add([4, 5, 6, 7, 2, 122]); expect v == 122, "test 1 failed";}
	{var v := add([4, 0, 6, 7]); expect v == 0, "test 2 failed";}
	{var v := add([4, 4, 6, 8]); expect v == 12, "test 3 failed";}
}