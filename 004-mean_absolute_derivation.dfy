function sum(s: seq<real>) : real {
  if |s| == 0 then 0.0 else s[0] + sum(s[1..])
}

lemma sum_prop(s: seq<real>)
  requires |s| > 0
  ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}

function abs(x: real) : real
  ensures abs(x) >= 0.0
{
  if x >= 0.0 then x else -x
}

function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}

method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)
  requires |numbers| > 0
  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
{
  var s: real := 0.0;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i])
  {
    s := s + numbers[i];
    assert sum(numbers[..i + 1]) == sum(numbers[..i]) + numbers[i] by { assert numbers[..i+1][..i] == numbers[..i]; sum_prop(numbers[..i + 1]); }
    i := i + 1;
  }

  var m := s / |numbers| as real;
  assert numbers[..|numbers|] == numbers;
  assert m == mean(numbers);

  var t: real := 0.0;
  i := 0;

  ghost var pref_seq := [];
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |pref_seq| == i
    invariant pref_seq == seq(i, j requires 0 <= j < i => abs(numbers[j] - m))
    invariant t == sum(pref_seq[..i])
  {
    ghost var pre_seq := pref_seq;
    assert pre_seq[..|pre_seq|] == pre_seq[..i] == pre_seq;

    pref_seq := pref_seq + [abs(numbers[i] - m)];

    assert sum(pref_seq[..i + 1]) == sum(pref_seq[..i]) + pref_seq[i] by { assert pref_seq[..i+1][..i] == pref_seq[..i]; sum_prop(pref_seq[..i + 1]); }

    t := t + abs(numbers[i] - m);
    i := i + 1;
  }

  assert pref_seq[..|pref_seq|] == pref_seq;
  derivation := t / |numbers| as real;
}
