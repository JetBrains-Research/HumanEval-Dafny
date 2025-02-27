method Main()
  decreases *
{
	{var v := count_distinct_characters(""); expect v == 0, "test 0 failed";}
	{var v := count_distinct_characters("abcde"); expect v == 5, "test 1 failed";}
	{var v := count_distinct_characters("abcdecadeCADE"); expect v == 5, "test 2 failed";}
	{var v := count_distinct_characters("aaaaAAAAaaaa"); expect v == 1, "test 3 failed";}
	{var v := count_distinct_characters("Jerry jERRY JeRRRY"); expect v == 5, "test 4 failed";}
}