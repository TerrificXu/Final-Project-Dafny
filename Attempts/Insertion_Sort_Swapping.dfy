predicate sorted(a:array<int>, min:int, max:int)
requires 0<= min <= max <= a.Length;
reads a;
{
  forall j, k :: min <= j < k < max ==> a[j] <= a[k]
}

predicate sorted'(a:seq<int>)
{
  forall j, k :: 0 <= j < k < |a| ==> a[j] <= a[k]
}

lemma sortedsubA(a:seq<int>, min:int, max:int)
requires 0<= min <= max <= |a|
requires sorted'(a)
ensures sorted'(a[min .. max])
{ }

method swap(a: array<int>, i:int, j:int)
  modifies a;
  requires 0 <= i < j < a.Length
  requires i + 1 == j
  ensures a[..i] == old(a[..i])
  ensures a[j+1..] == old(a[j+1..])
  ensures a[j] == old(a[i])
  ensures a[i] == old(a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
   var tmp := a[i];
   a[i] := a[j];
   a[j] := tmp;  
} 

method insertionSort(a: array<int>)
modifies a;
requires a.Length > 0;
ensures sorted(a, 0, a.Length);
ensures multiset(a[..]) == multiset(old(a[..])); 
{
  var i := 0;

  while(i < a.Length)
     invariant 0 <= i <= a.Length
     invariant sorted(a, 0, i) 
     invariant multiset(old(a[..])) == multiset(a[..]);
  {
     var key := a[i];

     var j := i - 1;

     ghost var a' := a[..];
     assert sorted'(a'[0..i]);
     while(j >= 0 && key < a[j])
        invariant -1 <= j <= i - 1
        invariant a[0 .. j+1] == a'[0 .. j+1]
        invariant sorted(a, 0, j+1);
        invariant a[j+1] == key == a'[i];
        invariant a[j+2 .. i+1] == a'[j+1 .. i]
        invariant sorted(a, j+2, i+1); 
        invariant multiset(old(a[..])) == multiset(a[..])
        invariant forall k :: j+1 < k <= i ==> key < a[k]                                     
     {
       ghost var a'' := a[..];
       swap(a, j, j+1);
       assert a[0..j] == a''[0..j];
       assert a[0..j] == a'[0..j];
       assert a[j] == a''[j+1] == a'[i] == key;
       assert a[j+2..] == a''[j+2..];
       assert a[j+2..i+1] == a''[j+2..i+1] == a'[j+1..i];

       j := j - 1;

       sortedsubA(a'[0..i], j+1, i);
       assert sorted'(a'[j+1..i]);
       assert a[j+2 .. i+1] == a'[j+1 .. i];
       assert sorted'(a[j+2..i+1]);
     }
     i := i + 1; 
  }
} 