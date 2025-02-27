method Main()
  decreases *
{
	{var v := by_length([2, 1, 1, 4, 5, 8, 2, 3]); expect v == ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"], "test 0 failed";}
	{var v := by_length([]); expect v == [], "test 1 failed";}
	{var v := by_length([1, -1, 55]); expect v == ["One"], "test 2 failed";}
	{var v := by_length([1, -1, 3, 2]); expect v == ["Three", "Two", "One"], "test 3 failed";}
	{var v := by_length([9, 4, 8]); expect v == ["Nine", "Eight", "Four"], "test 4 failed";}
}