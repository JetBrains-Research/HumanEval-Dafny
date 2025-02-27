method Main()
  decreases *
{
	{var v := get_closest_vowel("yogurt"); expect v == "u", "test 0 failed";}
	{var v := get_closest_vowel("full"); expect v == "u", "test 1 failed";}
	{var v := get_closest_vowel("easy"); expect v == "", "test 2 failed";}
	{var v := get_closest_vowel("eAsy"); expect v == "", "test 3 failed";}
	{var v := get_closest_vowel("ali"); expect v == "", "test 4 failed";}
	{var v := get_closest_vowel("bad"); expect v == "a", "test 5 failed";}
	{var v := get_closest_vowel("most"); expect v == "o", "test 6 failed";}
	{var v := get_closest_vowel("ab"); expect v == "", "test 7 failed";}
	{var v := get_closest_vowel("ba"); expect v == "", "test 8 failed";}
	{var v := get_closest_vowel("quick"); expect v == "", "test 9 failed";}
	{var v := get_closest_vowel("anime"); expect v == "i", "test 10 failed";}
	{var v := get_closest_vowel("Asia"); expect v == "", "test 11 failed";}
	{var v := get_closest_vowel("Above"); expect v == "o", "test 12 failed";}
}