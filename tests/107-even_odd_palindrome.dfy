method Main()
  decreases *
{
	{var s, p := even_odd_palindrome(123); expect [s, p] == [8, 13], "test 0 failed";}
	{var s, p := even_odd_palindrome(12); expect [s, p] == [4, 6], "test 1 failed";}
	{var s, p := even_odd_palindrome(3); expect [s, p] == [1, 2], "test 2 failed";}
	{var s, p := even_odd_palindrome(63); expect [s, p] == [6, 8], "test 3 failed";}
	{var s, p := even_odd_palindrome(25); expect [s, p] == [5, 6], "test 4 failed";}
	{var s, p := even_odd_palindrome(19); expect [s, p] == [4, 6], "test 5 failed";}
	{var s, p := even_odd_palindrome(9); expect [s, p] == [4, 5], "test 6 failed";}
	{var s, p := even_odd_palindrome(1); expect [s, p] == [0, 1], "test 7 failed";}
}