method Main()
  decreases *
{
	{var v := make_palindrome(""); expect v == "", "test 0 failed";}
	{var v := make_palindrome("x"); expect v == "x", "test 1 failed";}
	{var v := make_palindrome("xyz"); expect v == "xyzyx", "test 2 failed";}
	{var v := make_palindrome("xyx"); expect v == "xyx", "test 3 failed";}
	{var v := make_palindrome("jerry"); expect v == "jerryrrej", "test 4 failed";}
}