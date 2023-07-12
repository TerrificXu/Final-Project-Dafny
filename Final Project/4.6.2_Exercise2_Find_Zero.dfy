method findZero(a:array<int>) returns (pos:int, success:bool)
  requires a.Length > 0;
  ensures success <==> (exists i :: 0 <= i < a.Length &&  a[i] == 0);
  ensures 0 <= pos < a.Length;
  ensures success ==> a[pos] == 0;
{  
  var j := 0;
  while(j < a.Length)
    invariant 0 <= j <= a.Length;
    invariant forall k :: 0 <= k < j ==> a[k] != 0;
    // invariant 0 <= pos < a.Length;  
    // invariant success ==> a[pos] == 0;
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