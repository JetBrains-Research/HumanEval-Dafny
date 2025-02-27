method Main()
  decreases *
{
	{var v := histogram("a b b a"); expect v == map['a' := 2, 'b' := 2], "test 0 failed";}
	{var v := histogram("a b c a b"); expect v == map['a' := 2, 'b' := 2], "test 1 failed";}
	{var v := histogram("a b c d g"); expect v == map['a' := 1, 'b' := 1, 'c' := 1, 'd' := 1, 'g' := 1], "test 2 failed";}
	{var v := histogram("r t g"); expect v == map['r' := 1, 't' := 1, 'g' := 1], "test 3 failed";}
	{var v := histogram("b b b b a"); expect v == map['b' := 4], "test 4 failed";}
	{var v := histogram("r t g"); expect v == map['r' := 1, 't' := 1, 'g' := 1], "test 5 failed";}
	{var v := histogram(""); expect v == map[], "test 6 failed";}
	{var v := histogram("a"); expect v == map['a' := 1], "test 7 failed";}
}