method Main()
  decreases *
{
	{var v := Strongest_Extension("Watashi", ["tEN", "niNE", "eIGHt8OKe"]); expect v == "Watashi.eIGHt8OKe", "test 0 failed";}
	{var v := Strongest_Extension("Boku123", ["nani", "NazeDa", "YEs.WeCaNe", "32145tggg"]); expect v == "Boku123.YEs.WeCaNe", "test 1 failed";}
	{var v := Strongest_Extension("__YESIMHERE", ["t", "eMptY", "nothing", "zeR00", "NuLl__", "123NoooneB321"]); expect v == "__YESIMHERE.NuLl__", "test 2 failed";}
	{var v := Strongest_Extension("K", ["Ta", "TAR", "t234An", "cosSo"]); expect v == "K.TAR", "test 3 failed";}
	{var v := Strongest_Extension("__HAHA", ["Tab", "123", "781345", "-_-"]); expect v == "__HAHA.123", "test 4 failed";}
	{var v := Strongest_Extension("YameRore", ["HhAas", "okIWILL123", "WorkOut", "Fails", "-_-"]); expect v == "YameRore.okIWILL123", "test 5 failed";}
	{var v := Strongest_Extension("finNNalLLly", ["Die", "NowW", "Wow", "WoW"]); expect v == "finNNalLLly.WoW", "test 6 failed";}
	{var v := Strongest_Extension("_", ["Bb", "91245"]); expect v == "_.Bb", "test 7 failed";}
	{var v := Strongest_Extension("Sp", ["671235", "Bb"]); expect v == "Sp.671235", "test 8 failed";}
}