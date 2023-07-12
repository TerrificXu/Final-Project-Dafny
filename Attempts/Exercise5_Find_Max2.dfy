method findMax2(a:array<int>) returns (maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;

  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  
{

  var x := 0;
  var y := a.Length - 1;
  
  while(x != y)
    invariant true // COMPLETE
    invariant 0 <= x <= y < a.Length;
    
    invariant forall i :: (0 <= i < a.Length) && (a[x] <= a[y]) ==> a[i] <= a[y];
    invariant forall i :: (0 <= i < a.Length) && (a[x] >= a[y]) ==> a[i] <= a[x];
    
  
  {
    assert forall i :: (0 <= i < a.Length)  ==> a[i] <= maxVal;    
    if (a[x] <= a[y]) 
    {
      x := x + 1;
    }

    else
    {
      y := y - 1;
    }
    assert forall i :: (0 <= i < a.Length)  ==> a[i] <= a[x];
  }
  
  
  return a[x];

  


}

