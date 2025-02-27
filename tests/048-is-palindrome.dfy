method Main()
  decreases *
{
	{var v := is_palindrome(""); expect v == true, "test 0 failed";}
	{var v := is_palindrome("aba"); expect v == true, "test 1 failed";}
	{var v := is_palindrome("aaaaa"); expect v == true, "test 2 failed";}
	{var v := is_palindrome("zbcd"); expect v == false, "test 3 failed";}
	{var v := is_palindrome("xywyx"); expect v == true, "test 4 failed";}
	{var v := is_palindrome("xywyz"); expect v == false, "test 5 failed";}
	{var v := is_palindrome("xywzx"); expect v == false, "test 6 failed";}
}