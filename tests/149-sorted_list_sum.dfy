method Main()
  decreases *
{
	{var v := sorted_list_sum(["aa", "a", "aaa"]); expect v == ["aa"], "test 0 failed";}
	{var v := sorted_list_sum(["school", "AI", "asdf", "b"]); expect v == ["AI", "asdf", "school"], "test 1 failed";}
	{var v := sorted_list_sum(["d", "b", "c", "a"]); expect v == [], "test 2 failed";}
	{var v := sorted_list_sum(["d", "dcba", "abcd", "a"]); expect v == ["abcd", "dcba"], "test 3 failed";}
	{var v := sorted_list_sum(["AI", "ai", "au"]); expect v == ["AI", "ai", "au"], "test 4 failed";}
	{var v := sorted_list_sum(["a", "b", "b", "c", "c", "a"]); expect v == [], "test 5 failed";}
	{var v := sorted_list_sum(["aaaa", "bbbb", "dd", "cc"]); expect v == ["cc", "dd", "aaaa", "bbbb"], "test 6 failed";}
}