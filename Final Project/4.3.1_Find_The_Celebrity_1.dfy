predicate method People<W>(all: W, all': W)
  requires all != all'  

predicate isCelebrity<X>(guy: X, people: set<X>)
{
  guy in people &&
  forall person :: person in people && person != guy ==> People(person, guy) && !People(guy, person)
}

method findTheCelebrity'<Z>(people: set<Z>, guy: Z) returns (returnOne: Z)
  requires isCelebrity(guy, people)
  ensures returnOne == guy
{
  var P := people;
  var sb1 :| sb1 in P;  //use sb1 to represent somebody_1
  while P != {sb1}
    invariant isCelebrity(guy, P) 
    invariant sb1 in P
    decreases P  // The requirement for termination, since P is necessarily reduced after the loop, prevents infinite loops.
  {
    var sb2 :| sb2 in P - {sb1};
    if People(sb1, sb2) {
      P := P - {sb1};  
    } else {
      P := P - {sb2};  
    }
    sb1 :| sb1 in P;
  }
  returnOne := sb1;  // ensure that returnOne is still equal to guy
}

