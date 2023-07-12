method validateZero(a:array<int>) returns (pos:int, success:bool)

  ensures success <==> (forall i :: 0 <= i < a.Length ==>  a[i] == 0);
{
  var j := 0;
  while(j < a.Length)
    invariant 0 <= j <= a.Length;
    invariant forall i :: 0 <= i < j <= a.Length ==>  a[i] == 0;
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