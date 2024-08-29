method check_if_last_char_is_a_letter(s: string) returns (b: bool)
  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
{
  b := |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ');
}


predicate is_alpha(c: char) {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}