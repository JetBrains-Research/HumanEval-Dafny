method Main()
  decreases *
{
	{var v := solve("AsDf"); expect v == "aSdF", "test 0 failed";}
	{var v := solve("1234"); expect v == "4321", "test 1 failed";}
	{var v := solve("ab"); expect v == "AB", "test 2 failed";}
	{var v := solve("#a@C"); expect v == "#A@c", "test 3 failed";}
	{var v := solve("#AsdfW^45"); expect v == "#aSDFw^45", "test 4 failed";}
	{var v := solve("#6@2"); expect v == "2@6#", "test 5 failed";}
	{var v := solve("#$a^D"); expect v == "#$A^d", "test 6 failed";}
	{var v := solve("#ccc"); expect v == "#CCC", "test 7 failed";}
}