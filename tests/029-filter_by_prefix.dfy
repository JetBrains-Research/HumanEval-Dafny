method Main()
  decreases *
{
	{var v := filter_by_prefix([], "john"); expect v == [], "test 0 failed";}
	{var v := filter_by_prefix(["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"], "xxx"); expect v == ["xxx", "xxxAAA", "xxx"], "test 1 failed";}
}