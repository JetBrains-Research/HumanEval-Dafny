method Main()
  decreases *
{
	{var v := separate_paren_groups("(()()) ((())) () ((())()())"); expect v == ["(()())", "((()))", "()", "((())()())"], "test 0 failed";}
	{var v := separate_paren_groups("() (()) ((())) (((())))"); expect v == ["()", "(())", "((()))", "(((())))"], "test 1 failed";}
	{var v := separate_paren_groups("(()(())((())))"); expect v == ["(()(())((())))"], "test 2 failed";}
	{var v := separate_paren_groups("( ) (( )) (( )( ))"); expect v == ["()", "(())", "(()())"], "test 3 failed";}
}