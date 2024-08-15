function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}

predicate Happy(s: string) 
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}

method IsHappy(s: string) returns (happy : bool)
    ensures happy <==> Happy(s)
    {
        if |s| < 3 {
            return false;
        }

        var i := 1;
        while(i < |s| - 1) 
            invariant 0 < i <= |s| - 1
            invariant forall j :: 0 < j < i ==> ThreeDistinct(s, j)
        {
            if !ThreeDistinct(s, i) {
                return false;
            }
            i := i + 1;
        }
        return true;
    }