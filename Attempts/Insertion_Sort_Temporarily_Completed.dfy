
  reads a;
{  
	forall i,j :: from<=i<j<to && 0<=i<j<a.Length ==> a[i]<=a[j]
}

predicate sorted(a: array<int>)
	reads a;
{  
	sorted_between(a,0,a.Length) 
}



ghost method LemmaOne(a: array<int>, from:int, to:int, m:nat, n:nat)
	ensures sorted_between(a,from,to) ==> sorted_between(a,from+m,to-n);
 { }

 ghost method LemmaTwo(a: array<int>, from:int, to:int, m:nat, n:nat)
	requires from<=0 && to>=a.Length;
	ensures sorted_between(a,from,to) ==> sorted_between(a,from-m,to+n);
 { }


function count<T>(x: T, s: seq<T>): nat
{
  if (|s| == 0)
  then 0
  else
    if x == s[0]
    then 1 + count(x, s[1..])
    else count(x, s[1..])
}

ghost method prop_count_add<T>(x: T, s: seq<T>, t: seq<T>)
  ensures count(x,s+t) == count(x,s)+count(x,t);
 { 
   if (|s| == 0)
      { calc{ count(x,s+t);
            == { assert s+t==t; }
          count(x,t);
          ==
         0 + count(x,t);
          ==
         count(x,s)+count(x,t);   }         
      } 
  else if (x==s[0])
        {calc {count(x,s+t);
            ==  
            1 + count(x,(s+t)[1..]);
            == { assert (s+t)[1..] == s[1..]+t; }
            1 + count(x,s[1..]+t);
            ==
            1 + count(x,s[1..]) + count(x,t);
            ==
            count(x,s)+count(x,t);  } }
  else 
     { calc { count(x,s+t);
            ==  
             0 + count(x,(s+t)[1..]);
            == { assert (s+t)[1..] == s[1..]+t; }
            0 + count(x,s[1..]+t);
            ==
            0 + count(x,s[1..]) + count(x,t);
            ==
            count(x,s)+count(x,t);   } }
    /* var i := if (x==s[0]) then 1 else 0;
      calc{ count(x,s+t);
            ==  
            i + count(x,s[1..]+t);
            ==
            i + count(x,s[1..]) + count(x,t);
            ==
            count(x,s)+count(x,t);   } */
 }
  
  
predicate perm<T>(a: seq<T>, b: seq<T>) 
{
  forall x :: count(x, a) == count(x, b)
}

predicate perm_except<T>(a: seq<T>, b: seq<T>, j:nat, temp: T) 
   requires 0<=j<|a|  ;
{
  perm(a[0..j]+[temp]+a[j+1..], b)
}


ghost method perm_trans<T>(a: seq<T>, b: seq<T>,c: seq<T>)
    requires perm(a,b) && perm(b,c);
    ensures perm(a,c);
{    }

predicate same<T>(a:seq<T>, b:seq<T>)
     { |a|==|b| && ( forall k:: 0<=k<|a| ==> a[k]==b[k] ) }
     
ghost method same_implies_perm<T>(a: seq<T>, b: seq<T>) 
   requires same(a,b);
   ensures perm(a,b);
{  if |a|==0   {}  else { same_implies_perm(a[1..],b[1..]);}  }
 
ghost method id_implies_perm_except<T>(a: seq<T>, j:nat) 
   requires j<|a| ;
   ensures perm_except(a,a,j,a[j]);
{  var temp := a[0..j]+[a[j]]+a[j+1..];
  assert forall k:: 0<=k<|a| ==> a[k]==temp[k];  
  same_implies_perm(a,temp); }

ghost method perm_implies_perm_except<T>(a: seq<T>, b: seq<T>,j:nat) 
   requires perm(b,a) &&  j<|a| ;
   ensures perm_except(a,b,j,a[j]);
{ assert same(a, a[0..j]+[a[j]]+a[j+1..]);
  same_implies_perm(a,a[0..j]+[a[j]]+a[j+1..]);
  perm_trans(b,a,a[0..j]+[a[j]]+a[j+1..]);
}
 
 ghost method AuxLemma<T>(x:T, a:seq<T>,j:nat,temp:T)
    requires 0<j<|a|;
    ensures  count(x, a[0..j-1]+[temp]+[a[j-1]]+a[j+1..])
                       == 
                       count(x, a[0..j]+[temp]+a[j+1..]);
 {  calc {
     count(x, a[0..j-1]+[temp]+[a[j-1]]+a[j+1..]);
        ==   { prop_count_add(x,a[0..j-1]+[temp]+[a[j-1]],a[j+1..]); }
     count(x, a[0..j-1]+[temp]+[a[j-1]]) + count(x, a[j+1..]); 
        == { prop_count_add(x,a[0..j-1]+[temp],[a[j-1]]); } 
     count(x, a[0..j-1]+[temp]) + count(x,[a[j-1]]) + count(x,a[j+1..]);
        == { prop_count_add(x,a[0..j-1],[temp]); } 
     count(x, a[0..j-1]) + count(x, [temp]) +count(x,[a[j-1]])+count(x,a[j+1..]);  
        == 
     count(x, a[0..j-1]) +count(x,[a[j-1]]) + count(x, [temp]) +count(x,a[j+1..]);  
        == { prop_count_add(x,a[0..j-1],[a[j-1]]); }
     count(x, a[0..j-1]+[a[j-1]])  + count(x, [temp]) +count(x,a[j+1..]);
        == { prop_count_add(x,a[0..j-1]+[a[j-1]],[temp]); }
     count(x, a[0..j-1]+[a[j-1]]+[temp]) +count(x,a[j+1..]);
        == { assert a[0..j-1]+[a[j-1]] ==a[0..j];
             prop_count_add(x,a[0..j-1]+[a[j-1]]+[temp], a[j+1..]); }
     count(x, a[0..j]+[temp]+a[j+1..]);
 }} 
           
ghost method Lemma<T>(a: seq<T>, b: seq<T>, c: seq<T>, j: nat, temp: T)
     requires 0<j<|a| && perm_except(a,b,j,temp) && c==(a[..j]+[a[j-1]]+a[j+1..]);
     ensures perm_except(c,b,j-1,temp);
{
  assert c[0..j-1]+[temp]+c[j..] == a[0..j-1]+[temp]+[a[j-1]]+a[j+1..];
  forall x:T { AuxLemma(x,a,j,temp); }
  assert perm( a[0..j-1]+[temp]+[a[j-1]]+a[j+1..], a[0..j]+[temp]+a[j+1..]);
  assert perm(c[0..j-1]+[temp]+c[j..],a[0..j]+[temp]+a[j+1..]); 
  assert perm( c[0..j-1]+[temp]+c[j..], b); }
 
 
    
ghost method update_perm_except_implies_Perm<T>(a: seq<T>, b: seq<T>, c: seq<T>, j: nat, temp: T)
     requires 0<=j<|a|;
     requires perm_except(a,b,j,temp);
     requires c==(a[0..j]+[temp]+a[j+1..]);
     ensures perm(c,b) ;
 { 
 } 
 
     


method InsertionSorta(a: array<int>)
  modifies a;
  ensures sorted(a) && perm(a[..], old(a[..]) );
{
  var i := 1;

  if ( a.Length > 1) { id_implies_perm_except(a[..],i); } 
  assert a.Length < 2 || perm_except(a[..],old(a[..]),i,a[i]);
  
  while (i < a.Length)
    invariant a.Length < 2 ||  0 < i <= a.Length;
    invariant sorted_between(a,0,i) && perm(a[..], old(a[..]) );
  {
    var temp := a[i];
    
    perm_implies_perm_except(a[..],old(a[..]),i);
    assert perm_except(a[..],old(a[..]),i,temp);
    var j := i;
    while (j > 0 && temp <= a[j - 1])
      invariant 0 <= j <= i;
      invariant forall k :: j <= k < i ==> temp <= a[k];
      invariant sorted_between(a, 0, i);
      invariant ( j == i && sorted_between(a, 0, i) ) || sorted_between(a, 0, i+1);
      invariant perm_except(a[..],old(a[..]),j,temp);
      {   ghost var a_start := a[..];
          assert perm_except(a_start,old(a[..]),j,temp);
          
    	    a[j] := a[j - 1];
          
          ghost var a_end := a[..];
          Lemma(a_start,old(a[..]),a_end,j,temp);
          assert perm_except(a[..], old(a[..]),j-1,temp);
	        j := j - 1;
      }
	  ghost var a_start := a[..];
    a[j] := temp;
    ghost var a_end := a[..];
    update_perm_except_implies_Perm(a_start,old(a[..]),a_end,j,temp);
    i := i + 1;
  }
}