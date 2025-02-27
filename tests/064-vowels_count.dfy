method Main()
  decreases *
{
	{var v := vowels_count("abcde"); expect v == 2, "test 0 failed";}
	{var v := vowels_count("Alone"); expect v == 3, "test 1 failed";}
	{var v := vowels_count("key"); expect v == 2, "test 2 failed";}
	{var v := vowels_count("bye"); expect v == 1, "test 3 failed";}
	{var v := vowels_count("keY"); expect v == 2, "test 4 failed";}
	{var v := vowels_count("bYe"); expect v == 1, "test 5 failed";}
	{var v := vowels_count("ACEDY"); expect v == 3, "test 6 failed";}
}