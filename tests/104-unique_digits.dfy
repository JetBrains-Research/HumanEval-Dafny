method Main()
  decreases *
{
	{var v := unique_digits([15, 33, 1422, 1]); expect v == [1, 15, 33], "test 0 failed";}
	{var v := unique_digits([152, 323, 1422, 10]); expect v == [], "test 1 failed";}
	{var v := unique_digits([12345, 2033, 111, 151]); expect v == [111, 151], "test 2 failed";}
	{var v := unique_digits([135, 103, 31]); expect v == [31, 135], "test 3 failed";}
}