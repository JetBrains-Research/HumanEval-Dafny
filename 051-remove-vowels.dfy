function is_vowel(c: char) : bool
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

method remove_vowels(text : string) returns (s : string)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |s| ==> !is_vowel(s[i])
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && !is_vowel(text[j]) ==> text[j] in s
    // post-conditions-end
{
    // impl-start
    s := "";
    var i : int := 0;
    while (i < |text|)
        // invariants-start
        invariant 0 <= i && i <= |text|
        invariant forall i : int :: i >= 0 && i < |s| ==> !is_vowel(s[i])
        invariant forall i : int :: i >= 0 && i < |s| ==> s[i] in text
        invariant forall j : int :: j >= 0 && j < i && !is_vowel(text[j]) ==> text[j] in s
        // invariants-end
    {
        var c : char := text[i];
        if (!is_vowel(c))
        {
            s := s + [c];
        }
        i := i + 1;
    }
    // impl-end
}