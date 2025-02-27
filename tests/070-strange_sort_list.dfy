method Main()
  decreases *
{
	{var v := strange_sort_list([1, 2, 3, 4]); expect v == [1, 4, 2, 3], "test 0 failed";}
	{var v := strange_sort_list([5, 6, 7, 8, 9]); expect v == [5, 9, 6, 8, 7], "test 1 failed";}
	{var v := strange_sort_list([1, 2, 3, 4, 5]); expect v == [1, 5, 2, 4, 3], "test 2 failed";}
	{var v := strange_sort_list([5, 6, 7, 8, 9, 1]); expect v == [1, 9, 5, 8, 6, 7], "test 3 failed";}
	{var v := strange_sort_list([5, 5, 5, 5]); expect v == [5, 5, 5, 5], "test 4 failed";}
	{var v := strange_sort_list([]); expect v == [], "test 5 failed";}
	{var v := strange_sort_list([1, 2, 3, 4, 5, 6, 7, 8]); expect v == [1, 8, 2, 7, 3, 6, 4, 5], "test 6 failed";}
	{var v := strange_sort_list([0, 2, 2, 2, 5, 5, -5, -5]); expect v == [-5, 5, -5, 5, 0, 2, 2, 2], "test 7 failed";}
	{var v := strange_sort_list([111111]); expect v == [111111], "test 8 failed";}
}