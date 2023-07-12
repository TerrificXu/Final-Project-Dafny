// Invariant exercises
// July 2022

// Complete the invariants Dafny needs for each of the following 6 methods.
// For clarity, it is fine to write multiple invariant statements. E.g. write
//    invariant A;
//    invariant B;
// rather than
//    invariant A && B;
// In each case, start with invariants that establish bounds on variables and ensure 
// all the array index bound checks pass.

method validateZero(a:array<int>) returns (pos:int, success:bool)

  ensures success <==> (forall i :: 0 <= i < a.Length ==>  a[i] == 0);
{
  var j := 0;
  while(j < a.Length - 1)
    invariant j <= a.Length - 1;
    invariant forall j :: 0 <= j < a.Length ==>  a[j] == 0;
  {
    if (a[j] != 0)
    {
      success := false;
      return;
    }
    j := j+1;
  }
  success := true;
  return;
}

method findZero(a:array<int>) returns (pos:int, success:bool)
  requires a.Length > 0
  ensures success <==> (exists i :: 0 <= i < a.Length &&  a[i] == 0);
  ensures 0 <= pos < a.Length
  ensures success ==> a[pos] == 0;
{
  
  var j := 0;
  while(j < a.Length)
    invariant true // COMPLETE 
    invariant 0 <= j <= a.Length
    invariant exists i :: 0 <= i <j < a.Length &&  a[i] == 0


  {
    if (a[j] == 0)
    {
      success := true;
      pos := j;
      return;
    }
    j := j+1;
  }
  pos := 0; 
  success := false;
  return;
}

method incrementArray(a:array<int>)
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1;
  modifies a;
{
  var j : int := 0;
  while(j < a.Length)
    invariant true // COMPLETE
    
  {
    a[j] := a[j] + 1;
    j := j+1;
  }
}

method findMax(a:array<int>) returns (pos:int, maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;

  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  ensures exists i :: 0 <= i < a.Length &&  a[i] == maxVal;
  ensures 0 <= pos < a.Length
  ensures a[pos] == maxVal;
{
  pos := 0;
  maxVal := a[0];
  
  var j := 1;
  while(j < a.Length)
    
    invariant true // COMPLETE
  {
    if (a[j] > maxVal) 
    {
      maxVal := a[j];
      pos := j;
    }
    j := j+1;
  }
  return;
}

method findMax2(a:array<int>) returns (maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;

  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  
{

  var x := 0;
  var y := a.Length - 1;
  
  while(x != y)
    invariant true // COMPLETE
    
  {
    if (a[x] <= a[y]) 
    {
      x := x + 1;
    }
    else
    {
      y := y - 1;
    }
  }
  
  return a[x];
}

method binarySearch(a:array<int>, val:int) returns (pos:int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures 0 <= pos < a.Length ==> a[pos] == val
  ensures pos < 0 || pos >= a.Length  ==> forall i :: 0 <= i < a.Length ==> a[i] != val

{
  var left := 0;
  var right := a.Length - 1;
  if a[left] > val || a[right] < val 
  {
    return -1;
  }
  while left <= right
    invariant true // COMPLETE
    decreases right - left
  {
    var med := (left + right) / 2;
    assert left <= med <= right;
    if a[med] < val
    {
      left := med + 1;
    }
    else if a[med] > val
    {
      right := med - 1;
    }
    else
    {
      assert a[med] == val;
      pos := med;
      return;
    }

  }
  return -1;
}