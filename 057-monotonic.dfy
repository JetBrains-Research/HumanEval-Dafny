method monotonic(xs: seq<int>) returns (result: bool)
  requires |xs| > 0
  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])  
{
    if |xs| == 1 {
        return true;
    }

    var increasing := true;
    var decreasing := true;
    var i := 1;

    while i < |xs|
        invariant 1 <= i <= |xs|
        invariant increasing <==> (forall j, k :: 0 <= j < k < i ==> xs[j] < xs[k])
        invariant decreasing <==> (forall j, k :: 0 <= j < k < i ==> xs[j] > xs[k])
    {
        if xs[i - 1] >= xs[i] {
            increasing := false;
        }
        if xs[i - 1] <= xs[i] {
            decreasing := false;
        }
        i := i + 1;
    }

    result := increasing || decreasing;
}