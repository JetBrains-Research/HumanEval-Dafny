
method find_max(strings : seq<string>) returns (s : string) 
    requires |strings| > 0
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
{
    s := strings[0];
    var i := 1;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant s in strings[..i]
        invariant forall j : int :: 0 <= j < i ==> |set c | c in s| >= |set c | c in strings[j]|
    {
        if (|set c | c in s| < |set c | c in strings[i]|) {
            s := strings[i];
        }
        i := i + 1;
    }
}