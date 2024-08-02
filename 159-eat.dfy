method eat(number : int, need : int, remaining : int) returns (result: seq<int>)
  requires number >= 0 && need >= 0 && remaining >= 0
  ensures |result| == 2
  ensures remaining >= need ==> result[0] == number + need && result[1] == remaining - need
  ensures remaining < need ==> result[0] == number + remaining && result[1] == 0
{
  if remaining < need {
    result := [number + remaining, 0];
  } else {
    result := [number + need, remaining - need];
  }
}
