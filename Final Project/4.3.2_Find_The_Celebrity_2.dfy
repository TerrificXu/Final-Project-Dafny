predicate method People<W>(all: W, all': W)
  requires all != all'  

predicate isCelebrity<X>(guy: X, people: set<X>)
{
  guy in people &&
  forall person :: person in people && person != guy ==> People(person, guy) && !People(guy, person)
}

method findTheCelebrity''<V>(people: set<V>, guy: V) returns (returnOne: V)
  requires isCelebrity(guy, people)
  ensures returnOne == guy
{
  var all' :| all' in people;
  var remainingPeople := people - {all'};
  while remainingPeople != {}
    invariant remainingPeople <= people  // Obvious but not required
    invariant all' in people  // Obvious but not required
    invariant all' !in remainingPeople  // Ensure that the statement on line 24 does not report an error, Caring for line 2 statement
    invariant isCelebrity(guy, remainingPeople + {all'})  
    decreases remainingPeople
  {
    var remPeo :| remPeo in remainingPeople;
    if People(remPeo, all') {
      remainingPeople := remainingPeople - {remPeo};
    } else {
      all' := remPeo;
      remainingPeople := remainingPeople - {remPeo};
    }
  }
  returnOne := all';  // ensure that returnOne is still equal to guy
}
