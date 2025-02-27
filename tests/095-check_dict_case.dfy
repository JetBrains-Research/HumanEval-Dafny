method Main()
  decreases *
{
	{var v := check_dict_case(map["p" := "pineapple", "b" := "banana"]); expect v == true, "test 0 failed";}
	{var v := check_dict_case(map["p" := "pineapple", "b" := "banana"]); expect v == true, "test 1 failed";}
	{var v := check_dict_case(map["p" := "pineapple", "A" := "banana", "B" := "banana"]); expect v == false, "test 2 failed";}
	{var v := check_dict_case(map["p" := "pineapple", "A" := "banana", "B" := "banana"]); expect v == false, "test 3 failed";}
	{var v := check_dict_case(map["p" := "pineapple", "5" := "banana", "a" := "apple"]); expect v == false, "test 4 failed";}
	{var v := check_dict_case(map["p" := "pineapple", "5" := "banana", "a" := "apple"]); expect v == false, "test 5 failed";}
	{var v := check_dict_case(map["Name" := "John", "Age" := "36", "City" := "Houston"]); expect v == false, "test 6 failed";}
	{var v := check_dict_case(map["Name" := "John", "Age" := "36", "City" := "Houston"]); expect v == false, "test 7 failed";}
	{var v := check_dict_case(map["STATE" := "NC", "ZIP" := "12345"]); expect v == true, "test 8 failed";}
	{var v := check_dict_case(map["STATE" := "NC", "ZIP" := "12345"]); expect v == true, "test 9 failed";}
	{var v := check_dict_case(map["fruit" := "Orange", "taste" := "Sweet"]); expect v == true, "test 10 failed";}
	{var v := check_dict_case(map["fruit" := "Orange", "taste" := "Sweet"]); expect v == true, "test 11 failed";}
	{var v := check_dict_case(map[]); expect v == false, "test 12 failed";}
	{var v := check_dict_case(map[]); expect v == false, "test 13 failed";}
}