method Main()
  decreases *
{
	{var v := correct_bracketing("<>"); expect v == true, "test 0 failed";}
	{var v := correct_bracketing("<<><>>"); expect v == true, "test 1 failed";}
	{var v := correct_bracketing("<><><<><>><>"); expect v == true, "test 2 failed";}
	{var v := correct_bracketing("<><><<<><><>><>><<><><<>>>"); expect v == true, "test 3 failed";}
	{var v := correct_bracketing("<<<><>>>>"); expect v == false, "test 4 failed";}
	{var v := correct_bracketing("><<>"); expect v == false, "test 5 failed";}
	{var v := correct_bracketing("<"); expect v == false, "test 6 failed";}
	{var v := correct_bracketing("<<<<"); expect v == false, "test 7 failed";}
	{var v := correct_bracketing(">"); expect v == false, "test 8 failed";}
	{var v := correct_bracketing("<<>"); expect v == false, "test 9 failed";}
	{var v := correct_bracketing("<><><<><>><>><<>"); expect v == false, "test 10 failed";}
	{var v := correct_bracketing("<><><<><>><>>><>"); expect v == false, "test 11 failed";}
}