method Main()
  decreases *
{
	{var v := cycpattern_check("xyzw", "xyw"); expect v == false, "test 0 failed";}
	{var v := cycpattern_check("yello", "ell"); expect v == true, "test 1 failed";}
	{var v := cycpattern_check("whattup", "ptut"); expect v == false, "test 2 failed";}
	{var v := cycpattern_check("efef", "fee"); expect v == true, "test 3 failed";}
	{var v := cycpattern_check("abab", "aabb"); expect v == false, "test 4 failed";}
	{var v := cycpattern_check("winemtt", "tinem"); expect v == true, "test 5 failed";}
}