function IsValidParentheses(s: string, i: int, depth: int): bool
  decreases |s| - i
  requires 0 <= i && i <= |s|
{
    if i == |s| then
        depth >= 0
    else if depth < 0 then
        false
    else if s[i] == '(' then
        IsValidParentheses(s, i + 1, depth + 1)
    else if s[i] == ')' then
        depth > 0 && IsValidParentheses(s, i + 1, depth - 1)
    else
        IsValidParentheses(s, i + 1, depth)
}

function IsValidParentheses2(s: string, i: int, depth: int): bool
  decreases |s| - i
  requires 0 <= i && i <= |s|
{
    if i == |s| then
        depth == 0
    else if depth < 0 then
        false
    else if s[i] == '(' then
        IsValidParentheses2(s, i + 1, depth + 1)
    else if s[i] == ')' then
        if depth > 0 then IsValidParentheses2(s, i + 1, depth - 1) else false
    else
        IsValidParentheses2(s, i + 1, depth)
}

function IsValidParentheses1(s: string, i: int, depth: int): bool
  decreases |s| - i
  requires 0 <= i && i <= |s|
{
    if i == |s| then
        depth == 0
    else if (depth <= 0 && i != 0) then
        false
    else if s[i] == '(' then
        IsValidParentheses1(s, i + 1, depth + 1)
    else if s[i] == ')' then
        depth > 0 && IsValidParentheses1(s, i + 1, depth - 1)
    else
        IsValidParentheses1(s, i + 1, depth)
}

method separate_paren_groups(paren_string: string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')'
    requires forall i :: 0 <= i <= |paren_string| ==> IsValidParentheses(paren_string, i, 0)
    requires IsValidParentheses2(paren_string, 0, 0)
    // pre-conditions-end
    // post-conditions-start
    ensures |res| > 0 ==> forall i :: 0 <= i < |res| ==> IsValidParentheses1(res[i], 0, 0)
    // post-conditions-end
{
    // impl-start
    res := [];
    var current_string: string := "";
    var current_depth: int := 0;

    var i: int := 0;

    while (i < |paren_string|)
        // invariants-start
        invariant 0 <= i && i <= |paren_string|
        invariant 0 <= i && i < |paren_string| ==> paren_string[i] in {'(', ')'}
        invariant |res| > 0 ==> (forall i1 :: 0 <= i1 < |res| ==> IsValidParentheses1(res[i1], 0, 0))
        invariant IsValidParentheses(paren_string, i, 0)
        // invariants-end
    {
        var c: char := paren_string[i];
        if (c == '(')
        {
            current_depth := current_depth + 1;
            current_string := current_string + [c];
        }
        else if (c == ')')
        {
            current_depth := current_depth - 1;
            current_string := current_string + [c];

            if (current_depth == 0)
            {
                res := res + [current_string];
                current_string := "";
            }
        }
        i := i + 1;
    }
    // impl-end
}
