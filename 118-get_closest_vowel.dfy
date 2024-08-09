predicate IsVowel(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

predicate IsConsonant(c: char)
{
  ('A' <= c <= 'Z' || 'a' <= c <= 'z') && !IsVowel(c)
}

method get_closest_vowel(word: string) returns (result: string)
  requires forall i :: 0 <= i < |word| ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')
  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 1 ==> exists i {:trigger word[i]} :: 
        1 <= i && i + 1 < |word| 
            && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
            && (forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
{
  if |word| < 3 {
    return "";
  }

  var i := |word| - 2;
  while i > 0
    invariant 0 <= i <= |word| - 2
    invariant forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1])
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      return [word[i]];
    }
    i := i - 1;
  }

  return "";
}