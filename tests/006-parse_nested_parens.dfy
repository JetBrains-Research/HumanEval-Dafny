method Main()
  decreases *
{
	{var v := parse_nested_parens("(()()) ((())) () ((())()())"); expect v == [2, 3, 1, 3], "test 0 failed";}
	{var v := parse_nested_parens("() (()) ((())) (((())))"); expect v == [1, 2, 3, 4], "test 1 failed";}
	{var v := parse_nested_parens("(()(())((())))"); expect v == [4], "test 2 failed";}
}