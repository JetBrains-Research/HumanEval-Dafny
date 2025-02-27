method Main()
  decreases *
{
	{var v := all_prefixes(""); expect v == [], "test 0 failed";}
	{var v := all_prefixes("asdfgh"); expect v == ["a", "as", "asd", "asdf", "asdfg", "asdfgh"], "test 1 failed";}
	{var v := all_prefixes("WWW"); expect v == ["W", "WW", "WWW"], "test 2 failed";}
}