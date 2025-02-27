method Main()
  decreases *
{
	{var v := string_xor("111000", "101010"); expect v == "010010", "test 0 failed";}
	{var v := string_xor("1", "1"); expect v == "0", "test 1 failed";}
	{var v := string_xor("0101", "0000"); expect v == "0101", "test 2 failed";}
}