
method same_chars(s0 : string, s1 : string) returns (b : bool)
    ensures b == ((set i | i in s0) == (set i | i in s1))
{
    b := ((set i | i in s0) == (set i | i in s1));
} 
