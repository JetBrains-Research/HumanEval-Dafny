method Main()
  decreases *
{
	{var v := numerical_letter_grade([4.0, 3.0, 1.7, 2.0, 3.5]); expect v == ["A+", "B", "C-", "C", "A-"], "test 0 failed";}
	{var v := numerical_letter_grade([1.2]); expect v == ["D+"], "test 1 failed";}
	{var v := numerical_letter_grade([0.5]); expect v == ["D-"], "test 2 failed";}
	{var v := numerical_letter_grade([0.0]); expect v == ["E"], "test 3 failed";}
	{var v := numerical_letter_grade([1.0, 0.3, 1.5, 2.8, 3.3]); expect v == ["D", "D-", "C-", "B", "B+"], "test 4 failed";}
	{var v := numerical_letter_grade([0.0, 0.7]); expect v == ["E", "D-"], "test 5 failed";}
}