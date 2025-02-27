method Main()
  decreases *
{
	{var v := check_if_last_char_is_a_letter("apple"); expect v == false, "test 0 failed";}
	{var v := check_if_last_char_is_a_letter("apple pi e"); expect v == true, "test 1 failed";}
	{var v := check_if_last_char_is_a_letter("eeeee"); expect v == false, "test 2 failed";}
	{var v := check_if_last_char_is_a_letter("A"); expect v == true, "test 3 failed";}
	{var v := check_if_last_char_is_a_letter("Pumpkin pie "); expect v == false, "test 4 failed";}
	{var v := check_if_last_char_is_a_letter("Pumpkin pie 1"); expect v == false, "test 5 failed";}
	{var v := check_if_last_char_is_a_letter(""); expect v == false, "test 6 failed";}
	{var v := check_if_last_char_is_a_letter("eeeee e "); expect v == false, "test 7 failed";}
	{var v := check_if_last_char_is_a_letter("apple pie"); expect v == false, "test 8 failed";}
	{var v := check_if_last_char_is_a_letter("apple pi e "); expect v == false, "test 9 failed";}
}