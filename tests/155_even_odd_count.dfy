method Main()
  decreases *
{
	{var s, p := even_odd_count(7); expect [s, p] == [0, 1], "test 0 failed";}
	{var s, p := even_odd_count(-78); expect [s, p] == [1, 1], "test 1 failed";}
	{var s, p := even_odd_count(3452); expect [s, p] == [2, 2], "test 2 failed";}
	{var s, p := even_odd_count(346211); expect [s, p] == [3, 3], "test 3 failed";}
	{var s, p := even_odd_count(-345821); expect [s, p] == [3, 3], "test 4 failed";}
	{var s, p := even_odd_count(-2); expect [s, p] == [1, 0], "test 5 failed";}
	{var s, p := even_odd_count(-45347); expect [s, p] == [2, 3], "test 6 failed";}
	{var s, p := even_odd_count(0); expect [s, p] == [1, 0], "test 7 failed";}
}