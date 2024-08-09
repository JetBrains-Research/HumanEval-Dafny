predicate IsPrime(n: nat)
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

function min(a: int, b: int): int
{
  if a <= b then a else b
}

function max(a: int, b: int): int
{
  if a >= b then a else b
}

method Intersection(start1: int, end1: int, start2: int, end2: int) returns (result: string)
  requires start1 <= end1 && start2 <= end2
  ensures result == "YES" || result == "NO"
  ensures result == "YES" <==> 
    (max(start1, start2) <= min(end1, end2) && 
     IsPrime((min(end1, end2) - max(start1, start2) + 1) as nat))
{
  var intersectionStart := max(start1, start2);
  var intersectionEnd := min(end1, end2);
  
  if intersectionStart <= intersectionEnd {
    var length := (intersectionEnd - intersectionStart + 1) as nat;
    if IsPrime(length) {
      return "YES";
    }
  }
  
  return "NO";
}

method {:test} Main()
{
  var result1 := Intersection(1, 2, 2, 3);
  assert result1 == "NO";
  
  var result2 := Intersection(-1, 1, 0, 4);
  // The intersection is [0, 1], which has length 2, a prime number
  assert result2 == "YES";
  
  var result3 := Intersection(-3, -1, -5, 5);
  assert result3 == "YES";
  
  print "All tests passed!\n";
}