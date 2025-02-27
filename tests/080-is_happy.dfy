method Main()
  decreases *
{
	{var v := is_happy("a"); expect v == false, "test 0 failed";}
	{var v := is_happy("aa"); expect v == false, "test 1 failed";}
	{var v := is_happy("abcd"); expect v == true, "test 2 failed";}
	{var v := is_happy("aabb"); expect v == false, "test 3 failed";}
	{var v := is_happy("adb"); expect v == true, "test 4 failed";}
	{var v := is_happy("xyy"); expect v == false, "test 5 failed";}
	{var v := is_happy("iopaxpoi"); expect v == true, "test 6 failed";}
	{var v := is_happy("iopaxioi"); expect v == false, "test 7 failed";}
}