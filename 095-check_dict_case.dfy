predicate IsLowerCase(s: string)
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate IsUpperCase(s: string)
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}

method CheckDictCase(dict: map<string, string>) returns (result: bool)
  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
{
  if |dict| == 0 {
    return false;
  }

  var allLower := true;
  var allUpper := true;

  var keys := dict.Keys;
  while keys != {}
    invariant allLower ==> forall j :: j in dict.Keys - keys ==> IsLowerCase(j)
    invariant allUpper ==> forall j :: j in dict.Keys - keys ==> IsUpperCase(j)
    invariant !allLower ==> exists j :: j in dict.Keys - keys && !IsLowerCase(j)
    invariant !allUpper ==> exists j :: j in dict.Keys - keys && !IsUpperCase(j)
  {
    var k :| k in keys;
    if !IsLowerCase(k) {
      allLower := false;
    }
    if !IsUpperCase(k) {
      allUpper := false;
    }
    if !allLower && !allUpper {
      return false;
    }
    keys := keys - {k};
  }

  result := allLower || allUpper;
}