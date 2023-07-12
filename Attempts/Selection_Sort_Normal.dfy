predicate sorted(a:array<int>, i:int)
  requires 0 <= i <= a.Length;
  reads a;
  {
    forall k :: 0 < k < i ==> a[k-1] < a[k]
  }
method lookForMin(a:array<int>, i:int) returns(m:int)
  requires 0 <= i < a.Length;
  ensures i <= m < a.Length;
  ensures forall k :: i <= k < a.Length ==> a[k] >= a[m];
  {
    var j := i;
    m := i;
    while (j < a.Length)
      decreases a.Length - j
      invariant i <= j <= a.Length;
      invariant i <= m < a.Length;
      invariant forall k :: i <= k < j ==> a[k] >= a[m];
      {
        if(a[j] < a[m]){m := j;}
        j := j + 1;
      }
  }

method selectionSort(a:array<int>) returns(s:array<int>)
  modifies a;
  ensures sorted(s,s.Length);
{
  var c,m := 0,0;
  var t;
  s := a;
  assert s.Length == a.Length;
  while(c<s.Length)
    decreases s.Length-c;
    invariant 0 <= c <= s.Length;
    invariant c-1 <= m <= s.Length;
    invariant sorted(s,c);
  {
    m := lookForMin(s,c);
    assert forall k :: c <= k < s.Length ==> s[k] >= s[m];
    assert forall k :: 0 <= k < c ==> s[k] <= s[m];
    assert s[c] >= s[m];
    t := s[c];
    s[m] := t;
    s[c] := s[m];
    assert s[m] >= s[c];
    assert forall k :: c <= k < s.Length ==> s[k] >= s[c];
    c := c+1;
    assert  c+1 < s.Length ==> s[c-1] <= s[c];
  }
}