method Main()
  decreases *
{
	{var v := decimal_to_binary(0); expect v == "db0db", "test 0 failed";}
	{var v := decimal_to_binary(32); expect v == "db100000db", "test 1 failed";}
	{var v := decimal_to_binary(103); expect v == "db1100111db", "test 2 failed";}
	{var v := decimal_to_binary(15); expect v == "db1111db", "test 3 failed";}
}