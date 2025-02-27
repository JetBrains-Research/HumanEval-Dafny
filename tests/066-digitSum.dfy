method Main()
  decreases *
{
	{var v := digitSum(""); expect v == 0, "test 0 failed";}
	{var v := digitSum("abAB"); expect v == 131, "test 1 failed";}
	{var v := digitSum("abcCd"); expect v == 67, "test 2 failed";}
	{var v := digitSum("helloE"); expect v == 69, "test 3 failed";}
	{var v := digitSum("woArBld"); expect v == 131, "test 4 failed";}
	{var v := digitSum("aAaaaXa"); expect v == 153, "test 5 failed";}
	{var v := digitSum(" How are yOu?"); expect v == 151, "test 6 failed";}
	{var v := digitSum("You arE Very Smart"); expect v == 327, "test 7 failed";}
}