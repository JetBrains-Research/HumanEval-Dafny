method Main()
  decreases *
{
	{var v := same_chars("eabcdzzzz", "dddzzzzzzzddeddabc"); expect v == true, "test 0 failed";}
	{var v := same_chars("abcd", "dddddddabc"); expect v == true, "test 1 failed";}
	{var v := same_chars("dddddddabc", "abcd"); expect v == true, "test 2 failed";}
	{var v := same_chars("eabcd", "dddddddabc"); expect v == false, "test 3 failed";}
	{var v := same_chars("abcd", "dddddddabcf"); expect v == false, "test 4 failed";}
	{var v := same_chars("eabcdzzzz", "dddzzzzzzzddddabc"); expect v == false, "test 5 failed";}
	{var v := same_chars("aabb", "aaccc"); expect v == false, "test 6 failed";}
}