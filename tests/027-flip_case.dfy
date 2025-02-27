method Main()
  decreases *
{
	{var v := flip_case(""); expect v == "", "test 0 failed";}
	{var v := flip_case("Hello!"); expect v == "hELLO!", "test 1 failed";}
	{var v := flip_case("These violent delights have violent ends"); expect v == "tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS", "test 2 failed";}
}