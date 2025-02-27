method Main()
  decreases *
{
	{var v := filter_by_substring([], "john"); expect v == [], "test 0 failed";}
	{var v := filter_by_substring(["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"], "xxx"); expect v == ["xxx", "xxxAAA", "xxx"], "test 1 failed";}
	{var v := filter_by_substring(["xxx", "asd", "aaaxxy", "john doe", "xxxAAA", "xxx"], "xx"); expect v == ["xxx", "aaaxxy", "xxxAAA", "xxx"], "test 2 failed";}
	{var v := filter_by_substring(["grunt", "trumpet", "prune", "gruesome"], "run"); expect v == ["grunt", "prune"], "test 3 failed";}
}