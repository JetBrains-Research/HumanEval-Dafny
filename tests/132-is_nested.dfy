method Main()
  decreases *
{
	{var v := is_nested("[[]]"); expect v == true, "test 0 failed";}
	{var v := is_nested("[]]]]]]][[[[[]"); expect v == false, "test 1 failed";}
	{var v := is_nested("[][]"); expect v == false, "test 2 failed";}
	{var v := is_nested("[]"); expect v == false, "test 3 failed";}
	{var v := is_nested("[[[[]]]]"); expect v == true, "test 4 failed";}
	{var v := is_nested("[]]]]]]]]]]"); expect v == false, "test 5 failed";}
	{var v := is_nested("[][][[]]"); expect v == true, "test 6 failed";}
	{var v := is_nested("[[]"); expect v == false, "test 7 failed";}
	{var v := is_nested("[]]"); expect v == false, "test 8 failed";}
	{var v := is_nested("[[]][["); expect v == true, "test 9 failed";}
	{var v := is_nested("[[][]]"); expect v == true, "test 10 failed";}
	{var v := is_nested(""); expect v == false, "test 11 failed";}
	{var v := is_nested("[[[[[[[["); expect v == false, "test 12 failed";}
	{var v := is_nested("]]]]]]]]"); expect v == false, "test 13 failed";}
}