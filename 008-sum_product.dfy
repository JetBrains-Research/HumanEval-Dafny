function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

lemma sum_prop(s: seq<int>) 
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

lemma prod_prop(s: seq<int>) 
    requires |s| > 0
    ensures prod(s) == prod(s[..|s| - 1]) * s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}

method sum_product(numbers: seq<int>) returns (s : int, p : int)
    ensures s == sum(numbers)
    ensures p == prod(numbers)
 {
    assert numbers[..|numbers|] == numbers;
    s := 0;
    p := 1;
    var i := 0;
    while (i < |numbers|)
        invariant 0 <= i <= |numbers|
        invariant s == sum(numbers[..i])
        invariant p == prod(numbers[..i])
    {
        assert sum(numbers[..i + 1]) == sum(numbers[..i]) + numbers[i] by {
            assert numbers[..i+1][..i] == numbers[..i];
            sum_prop(numbers[..i + 1]); 
        }
        s := s + numbers[i];

        assert prod(numbers[..i + 1]) == prod(numbers[..i]) * numbers[i] by {
            assert numbers[..i+1][..i] == numbers[..i];
            prod_prop(numbers[..i + 1]); 
        }
        p := p * numbers[i];

        i := i + 1;
    }
    
    return s, p;
}