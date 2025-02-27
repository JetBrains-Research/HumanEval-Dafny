method Main()
  decreases *
{
	{var v := total_match([], []); expect v == [], "test 0 failed";}
	{var v := total_match(["hi", "admin"], ["hi", "hi"]); expect v == ["hi", "hi"], "test 1 failed";}
	{var v := total_match(["hi", "admin"], ["hi", "hi", "admin", "project"]); expect v == ["hi", "admin"], "test 2 failed";}
	{var v := total_match(["4"], ["1", "2", "3", "4", "5"]); expect v == ["4"], "test 3 failed";}
	{var v := total_match(["hi", "admin"], ["hI", "Hi"]); expect v == ["hI", "Hi"], "test 4 failed";}
	{var v := total_match(["hi", "admin"], ["hI", "hi", "hi"]); expect v == ["hI", "hi", "hi"], "test 5 failed";}
	{var v := total_match(["hi", "admin"], ["hI", "hi", "hii"]); expect v == ["hi", "admin"], "test 6 failed";}
	{var v := total_match([], ["this"]); expect v == [], "test 7 failed";}
	{var v := total_match(["this"], []); expect v == [], "test 8 failed";}
}