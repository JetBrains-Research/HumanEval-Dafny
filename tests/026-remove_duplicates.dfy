method Main()
  decreases *
{
	{var v := remove_duplicates([]); expect v == [], "test 0 failed";}
	{var v := remove_duplicates([1, 2, 3, 4]); expect v == [1, 2, 3, 4], "test 1 failed";}
	{var v := remove_duplicates([1, 2, 3, 2, 4, 3, 5]); expect v == [1, 4, 5], "test 2 failed";}
}