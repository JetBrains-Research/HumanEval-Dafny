method Main()
  decreases *
{
	{var v := encode("TEST"); expect v == "tgst", "test 0 failed";}
	{var v := encode("Mudasir"); expect v == "mWDCSKR", "test 1 failed";}
	{var v := encode("YES"); expect v == "ygs", "test 2 failed";}
	{var v := encode("This is a message"); expect v == "tHKS KS C MGSSCGG", "test 3 failed";}
	{var v := encode("I DoNt KnOw WhAt tO WrItE"); expect v == "k dQnT kNqW wHcT Tq wRkTg", "test 4 failed";}
}