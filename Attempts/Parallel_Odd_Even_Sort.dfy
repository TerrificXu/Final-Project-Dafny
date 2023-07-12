predicate sortOdd(Seq: seq<int>) {
  forall idx :: 0 <= idx <= |Seq|-2 && idx % 2 == 1 ==> Seq[idx] <= Seq[idx+1] }

predicate sortEven(Seq: seq<int>) {
  forall idx :: 0 <= idx <= |Seq|-2 && idx % 2 == 0 ==> Seq[idx] <= Seq[idx+1] }

predicate isSorted(Seq: seq<int>) {
  forall idx :: forall idx' :: 0 <= idx <= idx' < |Seq| ==> Seq[idx] <= Seq[idx'] }

lemma Lemma_1(Seq: seq<int>)
  requires sortOdd(Seq)
  requires sortEven(Seq)
  ensures isSorted(Seq)
  // decreases can be omitted
{
  if |Seq| <= 2 {

  } else {
    assert Seq[0] <= Seq[1] <= Seq[2];
    Lemma_1(Seq[2..]);
  }
}


method parallelOddEvenSort(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures isSorted(a[..])
  decreases *
{
  var ifSorted := false;
  while(ifSorted == false)
    invariant ifSorted ==> isSorted(a[..])
    decreases *
  {
    ifSorted := true;
    var idx := 1;  // Make sure the indexes are all odd, using 1
    while (idx <= a.Length-2)
      invariant 0 <= idx <= a.Length
      invariant idx % 2 == 1
      invariant sortOdd(a[0..idx]) // a[1] <= a[2], a[3] <= a[4] ..
    {
      if (a[idx] > a[idx+1]) {
        a[idx], a[idx+1] := a[idx+1], a[idx];
        // ifSorted := false; // Originally written for understanding, this statement is not actually needed.
      }
      assert idx == 1 ==> a[1] <= a[2];

      assert a[idx] <= a[idx+1];

      idx := idx + 2;  // Continue to make sure the Seq numbers are all odd
    }
    // Arraay == [a[0], a[1], a[2], a[3], a[4], a[5], ... a[n-1]]
    assert sortOdd(a[..]);
    // a[1] <= a[2], a[3] <= a[4], a[5] <= a[6], ... a[n-2] <= a[n-1] if n odd.

    idx := 0;  // Make sure the indexes are all even, using 0
    var currentArray := a[..];
    while (idx <= a.Length-2)
      invariant ifSorted ==> a[..] == currentArray
      invariant 0 <= idx <= a.Length
      invariant idx % 2 == 0
      invariant sortEven(a[0..idx])
    {
      if (a[idx] > a[idx+1]) {
        a[idx], a[idx+1] := a[idx+1], a[idx];
        ifSorted := false;  // The reason why it cannot be omitted here is that the invariant of the 70th line need to be matched
                            // The purpose of currentArray is that I need to carry the previous odd sorted a.
      }
      assert idx == 0 ==> a[0] <= a[1];

      assert a[idx] <= a[idx+1];

      idx := idx + 2; // // Continue to make sure the Seq numbers are all even
    }
    assert sortEven(a[..]);
    //assert ifSorted ==> sortOdd(a[..]) && sortEven(a[..]);
    calc {
      sortOdd(a[..]) && sortEven(a[..]);
      ==> {Lemma_1(a[..]);}
      isSorted(a[..]);
    }
    assert ifSorted ==> isSorted(a[..]);  
  }
}