 function IsPrimeHexDigit(c: char): bool
{
  c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

function count_prime_hex_digits_rec(num: seq<char>) : (count : int)
  ensures 0 <= count <= |num|
{
  if |num| == 0 then 0
  else (if IsPrimeHexDigit(num[0]) then 1 else 0) + count_prime_hex_digits_rec(num[1..])
}

lemma count_prop(s: seq<char>) 
    requires |s| > 0
    ensures count_prime_hex_digits_rec(s) == count_prime_hex_digits_rec(s[..|s| - 1]) + (
        if IsPrimeHexDigit(s[ |s| - 1 ]) then 1 else 0
    )
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

method count_prime_hex_digits(s: seq<char>) returns (count : int)
    ensures count == count_prime_hex_digits_rec(s)
    ensures 0 <= count <= |s|
{
    count := 0;
    var i := 0;
    while(i < |s|) 
        invariant 0 <= i <= |s|
        invariant count == count_prime_hex_digits_rec(s[..i])
    {
        assert count_prime_hex_digits_rec(s[..i + 1]) == count_prime_hex_digits_rec(s[..i]) + (
            if IsPrimeHexDigit(s[ i ]) then 1 else 0
        ) by {
            assert s[..i+1][..i] == s[..i];
            count_prop(s[..i + 1]);
        }
        count := count + if IsPrimeHexDigit(s[i]) then 1 else 0;
        i := i + 1;
    }
    assert s[..i] == s;
    return count;
}