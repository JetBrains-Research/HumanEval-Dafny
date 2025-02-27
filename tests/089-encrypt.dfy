method Main()
  decreases *
{
	{var v := encrypt("hi"); expect v == "lm", "test 0 failed";}
	{var v := encrypt("asdfghjkl"); expect v == "ewhjklnop", "test 1 failed";}
	{var v := encrypt("gf"); expect v == "kj", "test 2 failed";}
	{var v := encrypt("et"); expect v == "ix", "test 3 failed";}
	{var v := encrypt("faewfawefaewg"); expect v == "jeiajeaijeiak", "test 4 failed";}
	{var v := encrypt("hellomyfriend"); expect v == "lippsqcjvmirh", "test 5 failed";}
	{var v := encrypt("dxzdlmnilfuhmilufhlihufnmlimnufhlimnufhfucufh"); expect v == "hbdhpqrmpjylqmpyjlpmlyjrqpmqryjlpmqryjljygyjl", "test 6 failed";}
	{var v := encrypt("a"); expect v == "e", "test 7 failed";}
}