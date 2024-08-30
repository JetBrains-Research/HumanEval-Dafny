method xor(a : char, b : char) returns (result : char)
    // post-conditions-start
    ensures result == (if a == b then '0' else '1')
    // post-conditions-end
{
    // impl-start
    if (a == b) {
        result := '0';
    } else {
        result := '1';
    }
    // impl-end
}

method string_xor(a: string, b: string) returns (result: string)
    // pre-conditions-start
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> (a[i] == '0' || a[i] == '1')
    requires forall i :: 0 <= i < |b| ==> (b[i] == '0' || b[i] == '1')
    // pre-conditions-end
    // post-conditions-start
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> (result[i] == '0' || result[i] == '1')
    ensures forall i :: 0 <= i < |result| ==> result[i] == (if a[i] == b[i] then '0' else '1')
    // post-conditions-end
{
    // impl-start
    result := "";
    var i : int := 0;
    while (i < |a|)
        // invariants-start
        invariant i >= 0 && i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == (if a[j] == b[j] then '0' else '1')
        // invariants-end
    {
        var bitResult := if a[i] == b[i] then '0' else '1';
        result := result + [bitResult];
        i := i + 1;
    }
    // impl-end
}
