method Main()
  decreases *
{
	{var v := longest([]); expect v == None, "test 0 failed";}
	{var v := longest(["x", "y", "z"]); expect v == Some("x"), "test 1 failed";}
	{var v := longest(["x", "yyy", "zzzz", "www", "kkkk", "abc"]); expect v == Some("zzzz"), "test 2 failed";}
}