method Main()
  decreases *
{
	{var v := remove_vowels(""); expect v == "", "test 0 failed";}
	{var v := remove_vowels("abcdef\nghijklm"); expect v == "bcdf\nghjklm", "test 1 failed";}
	{var v := remove_vowels("fedcba"); expect v == "fdcb", "test 2 failed";}
	{var v := remove_vowels("eeeee"); expect v == "", "test 3 failed";}
	{var v := remove_vowels("acBAA"); expect v == "cB", "test 4 failed";}
	{var v := remove_vowels("EcBOO"); expect v == "cB", "test 5 failed";}
	{var v := remove_vowels("ybcd"); expect v == "ybcd", "test 6 failed";}
}