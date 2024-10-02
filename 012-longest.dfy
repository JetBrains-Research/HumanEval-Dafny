datatype Option<T> = None | Some(T)

function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

method longest(strings: seq<string>) returns (result : Option<string>)
  // post-conditions-start
  ensures result == None <==> |strings| == 0
  ensures result != None ==> forall s :: s in strings ==> |getVal(result)| >= |s|
  ensures result != None ==> getVal(result) in strings 
  // post-conditions-end
{
    // impl-start
    result := None;
    var i : int := 0;
    var mx : int := -1;
    while (i < |strings|)
        // invariants-start
        invariant 0 <= i <= |strings|
        invariant i == 0 <==> mx == -1
        invariant forall s :: s in strings[0..i] ==> mx >= |s|
        invariant result == None <==> mx == -1
        invariant result != None ==> mx == |getVal(result)|
        invariant result != None ==> getVal(result) in strings
        // invariants-end
    {
        if (|strings[i]| > mx) {
            mx := |strings[i]|;
            result := Some(strings[i]);
        }
        i := i + 1;
    }
    // impl-end
}
