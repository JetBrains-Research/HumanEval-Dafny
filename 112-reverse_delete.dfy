method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
{
  res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall i :: 0 <= i < |res| ==> res[i] !in chars
    invariant forall i :: 0 <= i < |res| ==> res[i] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in res
  {
    if s[i] !in chars {
      res := res + [s[i]];
    }
    i := i + 1;
  }

  is_palindrome := check_palindrome(res);
}

method check_palindrome(s: string) returns (result: bool)
  ensures result <==> is_palindrome_pred(s)
{
  if |s| == 0 {
    return true;
  }
  result := true;
  var i := 0;
  var j := |s| - 1;
  while (i < j)
    invariant 0 <= i < |s|
    invariant 0 <= j < |s|
    invariant j == |s| - i - 1
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
  {
    if (s[i] != s[j]) {
      result := false;
      break;
    }
    i := i + 1;
    j := j - 1;
  }
}

predicate is_palindrome_pred(s : string) {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}