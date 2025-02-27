method Main()
  decreases *
{
	{var v := hex_key("AB"); expect v == 1, "test 0 failed";}
	{var v := hex_key("AB"); expect v == 1, "test 1 failed";}
	{var v := hex_key("1077E"); expect v == 2, "test 2 failed";}
	{var v := hex_key("1077E"); expect v == 2, "test 3 failed";}
	{var v := hex_key("ABED1A33"); expect v == 4, "test 4 failed";}
	{var v := hex_key("ABED1A33"); expect v == 4, "test 5 failed";}
	{var v := hex_key("2020"); expect v == 2, "test 6 failed";}
	{var v := hex_key("2020"); expect v == 2, "test 7 failed";}
	{var v := hex_key("123456789ABCDEF0"); expect v == 6, "test 8 failed";}
	{var v := hex_key("123456789ABCDEF0"); expect v == 6, "test 9 failed";}
	{var v := hex_key("112233445566778899AABBCCDDEEFF00"); expect v == 12, "test 10 failed";}
	{var v := hex_key("112233445566778899AABBCCDDEEFF00"); expect v == 12, "test 11 failed";}
	{var v := hex_key([]); expect v == 0, "test 12 failed";}
}