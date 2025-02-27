method Main()
  decreases *
{
	{var s, p := reverse_delete("abcde", "ae"); expect (s == "bcd" && p == false), "test 0 failed";}
	{var s, p := reverse_delete("abcdef", "b"); expect (s == "acdef" && p == false), "test 1 failed";}
	{var s, p := reverse_delete("abcdedcba", "ab"); expect (s == "cdedc" && p == true), "test 2 failed";}
	{var s, p := reverse_delete("dwik", "w"); expect (s == "dik" && p == false), "test 3 failed";}
	{var s, p := reverse_delete("a", "a"); expect (s == "" && p == true), "test 4 failed";}
	{var s, p := reverse_delete("abcdedcba", ""); expect (s == "abcdedcba" && p == true), "test 5 failed";}
	{var s, p := reverse_delete("abcdedcba", "v"); expect (s == "abcdedcba" && p == true), "test 6 failed";}
	{var s, p := reverse_delete("vabba", "v"); expect (s == "abba" && p == true), "test 7 failed";}
	{var s, p := reverse_delete("mamma", "mia"); expect (s == "" && p == true), "test 8 failed";}
}