predicate method People<W>(all: W, all': W)
  requires all != all'  

predicate isCelebrity<X>(guy: X, people: set<X>)
{
  guy in people &&
  forall person :: person in people && person != guy ==> People(person, guy) && !People(guy, person)
}

method findTheCelebrity'''(n: int, people: set<int>, guy: int) returns (returnOne: int)
  requires 0 < n
  requires forall person :: person in people <==> 0 <= person < n
  requires isCelebrity(guy, people)
  ensures returnOne == guy
{
  returnOne := 0;
  var all := 1;
  var all' := 0;
  while all < n
    invariant all <= n // Obvious but not required
    invariant all' < all  // This needs to stay the same from start to finish
    invariant guy == all' || (all <= guy < n)  // This satisfies the double-headed arrow on the 12 line
  {
    if People(all, all') {
      all := all + 1;
    } else {
      all' := all;
      all := all + 1;
    }
  }
  returnOne := all';  // ensure that returnOne is still equal to guy
}
