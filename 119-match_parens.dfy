function CalcBal(s: string, i: int, j: int, acc: int) : int
    requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == '(' then 1 else -1) + CalcBal(s, i, j - 1, acc)
}
// pure-end
method match_parens(s1: string, s2: string) returns (b: string)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s1| ==> s1[i] == '(' || s1[i] == ')'
    requires forall i :: 0 <= i < |s2| ==> s2[i] == '(' || s2[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures (b == "Yes") || (b == "No")
    ensures (b == "Yes") ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures (b == "Yes") ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures (b == "No") ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
    // post-conditions-end
{
    // impl-start
    var bal := 0;
    var i := 0;
    while i < |s1|
        // invariants-start
        invariant 0 <= i <= |s1|
        invariant bal == CalcBal(s1, 0, i, 0)
        invariant forall j :: 0 <= j < i ==> CalcBal(s1, 0, j, 0) >= 0
        // invariants-end
    {
        if s1[i] == '(' {
            bal := bal + 1;
        } else {
            bal := bal - 1;
        }
        if bal < 0 {
            // assert-start
            assert CalcBal(s1, 0, i + 1, 0) < 0;
            // assert-end
            return "No";
        }
        i := i + 1;
    }

    i := 0;
    while i < |s2| 
        // invariants-start
        invariant 0 <= i <= |s2|
        invariant bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) 
        invariant forall j :: 0 <= j < i ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0) >= 0
        // invariants-end
    {
        if s2[i] == '(' {
            bal := bal + 1;
        } else {
            bal := bal - 1;
        }
        if bal < 0 {
            // assert-start
            assert CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i + 1, 0) < 0;
            assert exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0;
            // assert-end
            return "No";
        }
        i := i + 1;
    }
    return "Yes";
    // impl-end
}
