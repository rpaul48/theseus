#lang forge

option problem_type temporal
option max_tracelength 24

--================================== SIGS ==================================--

abstract sig Player {
  var location: one Square
}

one sig Theseus extends Player {}
one sig Minotaur extends Player {}

one sig Game { 
  var turn: one PossibleTurn
}

abstract sig PossibleTurn {
  next: one PossibleTurn
}

// three turns for convenience of expressing turn order
one sig MinotaurTurn1 extends PossibleTurn {}
one sig MinotaurTurn2 extends PossibleTurn {}
one sig TheseusTurn extends PossibleTurn {}

sig Square {
  row: one Int,
  col: one Int,
  connections: set Square
}

one sig Exit {
  position: one Square
}

--================================== VALIDITY ==================================--

pred validConnections {
  -- symmetric
  connections = ~connections

  -- non reflexive
  no iden & connections

  -- can only have connections to adjacent squares
  all sq1, sq2: Square | sq1->sq2 in connections => {
    ((abs[subtract[sum[sq1.row], sum[sq2.row]]] = 1) and sq1.col = sq2.col)
    or ((abs[subtract[sum[sq1.col], sum[sq2.col]]] = 1) and sq1.row = sq2.row)
  }

  -- path between all pairs of squares
  all sq1, sq2: Square | sq1 in sq2.^connections
}

pred validGame {
  -- Setup turn order
  next = MinotaurTurn1->MinotaurTurn2 + MinotaurTurn2->TheseusTurn + TheseusTurn->MinotaurTurn1

  -- fixed maze grid size of 4x4
  -- 0-3 rows/columns
  all sq: Square | {
    sum[sq.row] >= 0 and sum[sq.row] < 4
    sum[sq.col] >= 0 and sum[sq.col] < 4
  }

  -- all squares occupy distinct grid places
  all sq1, sq2: Square | {
    {(sq1.col = sq2.col) and (sq1.row = sq2.row)} iff sq1 = sq2
  }

  #Square = 16

  -- exit location is valid
  (Exit.position).row = sing[3]
  (Exit.position).col = sing[3]

  validConnections
}

pred init{
  -- constrain initial theseus position
  Theseus.location != Exit.position
  
  -- constrain initial minotaur position
  Minotaur.location != Theseus.location

  -- theseus moves first
  Game.turn = TheseusTurn
}

--================================== BASIC MOVES ==================================--

// HELPER FUNCTIONS
fun getDist[s1: Square, s2: Square]: Int {
  sing[add[abs[subtract[sum[s1.row], sum[s2.row]]], abs[subtract[sum[s1.col], sum[s2.col]]]]]
}

// determines whether move from start -> end will move Minotaur closer to Theseus
pred closerToTheseus[start: Square, end: Square] {
  sum[getDist[start, Theseus.location]] > sum[getDist[end, Theseus.location]]
}

// determines whether move from start -> end will move Player closer to exit
pred closerToExit[start: Square, end: Square] {
  sum[getDist[start, Exit.position]] > sum[getDist[end, Exit.position]]
}

// determines whether move from start -> end will move Theseus farther from Minotaur
pred fartherFromMinotaur[start: Square, end: Square] {
  sum[getDist[start, Minotaur.location]] < sum[getDist[end, Minotaur.location]]
}

// MOVES
pred doNothing {
  location' = location
}

pred theseusMove {
  -- Minotaur doesn't move
  Minotaur.location = Minotaur.(location')

  -- Don't move to where the minotaur is
  Theseus.location' != Minotaur.location

  -- If Theseus can go to the exit, go to the exit
  Exit.position in (Theseus.location).connections => {Theseus.location' = Exit.position}
  Theseus.location' in (Theseus.location).connections
}

pred minotaurMove {
  -- Theseus doesn't move
  Theseus.location = Theseus.(location')
  
  { some sq: (Minotaur.location).connections | {
    closerToTheseus[Minotaur.location, sq] 
    sq.row = (Minotaur.location).row
  }} => {
    (Minotaur.(location')).row = (Minotaur.location).row
    (Minotaur.(location')) in (Minotaur.location).connections
    closerToTheseus[Minotaur.location, Minotaur.(location')]
  } else {
    { some sq: (Minotaur.location).connections | { 
      closerToTheseus[Minotaur.location, sq] 
    }} => {
      (Minotaur.(location')) in (Minotaur.location).connections
      closerToTheseus[Minotaur.location, Minotaur.(location')]
    } else {
      doNothing
    } 
  }
}

--================================== THESEUS STRATEGIES ==================================--

pred theseusMoveToExit {
  Minotaur.location = Minotaur.(location')

  -- Necessary constraints for theseus not to be dumb
  Theseus.location' != Minotaur.location
  Exit.position in (Theseus.location).connections => {Theseus.location' = Exit.position}
  
  { some sq: (Theseus.location).connections | { 
    closerToExit[Theseus.location, sq] 
  }} => {
    (Theseus.(location')) in (Theseus.location).connections
    closerToExit[Theseus.location, Theseus.(location')]
  } else {
    -- If no moves get him closer to exit, then he should just move closer
    -- (this is to prevent Theseus deadlock)
    Theseus.location' in (Theseus.location).connections
  }
}

pred theseusAwayFromMinotaur {
  Minotaur.location = Minotaur.(location')

  -- Necessary constraints for theseus not to be dumb
  Theseus.location' != Minotaur.location
  Exit.position in (Theseus.location).connections => {Theseus.location' = Exit.position}
  
  { some sq: (Theseus.location).connections | { 
    fartherFromMinotaur[Theseus.location, sq] 
  }} => {
    (Theseus.(location')) in (Theseus.location).connections
    fartherFromMinotaur[Theseus.location, Theseus.(location')]
  } else {
    -- If no moves get him closer to exit, then he should just move closer
    -- (this is to prevent Theseus deadlock)
    Theseus.location' in (Theseus.location).connections
  }
}

--================================== BASIC OUTCOMES ==================================--

pred win {
  Theseus.location in Exit.position
}

pred lose {
  Minotaur.location in Theseus.location
}

pred traces {
  validGame
  init
  
  -- Regulate who can move at each turn
  always {
    Game.turn = TheseusTurn => {
      theseusMove or doNothing
    } else {
      minotaurMove
    }
  }

  -- Turn must always change
  always (Game.turn' = (Game.turn).next)

  -- Game stops when we win or lose
  always ((win => always doNothing) and (lose => always doNothing))
}

--================================== SPECIAL OUTCOMES ==================================--

pred tracesWithWin {
  traces
  eventually win
}

pred tracesWithLose {
  traces
  eventually lose
}

pred tracesWithTheseusMoveToExit {
  validGame
  init
  
  -- Regulate who can move at each turn
  always {
    Game.turn = TheseusTurn => {
      theseusMoveToExit or doNothing
    } else {
      minotaurMove
    }
  }

  -- Turn must always change
  always (Game.turn' = (Game.turn).next)

  -- Game stops when we win or lose
  always ((win => always doNothing) and (lose => always doNothing))
}

pred interesting {
  -- Ensure that theseus starts at least 2 from the exist
  sum[getDist[Theseus.location, Exit.position]] > 3
  // sum[getDist[Theseus.location, Minotaur.location]] > 2
}

// run {
//   Theseus.location in (Minotaur.location).connections
//   tracesWithWin
//   interesting
// } for 16 Square, exactly 5 Int, exactly 3 PossibleTurn

// run {
//   tracesWithTheseusMoveToExit
//   eventually(lose)
//   interesting
// } for 16 Square, exactly 5 Int, exactly 3 PossibleTurn


--=========================== INTERESTING EXAMPLES ===========================--

// See video for instance
inst mazeWithFakeOut {
  /*
  Minotaur at column 0 row 2. Theseus at column 2, row 0
  E: Exit
   _ _ _ _
  |    _  |
  |    _| |
  |M      |
  |_ _ _ E|
  */

  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + Square6 
  + Square7 + Square8 + Square9 + Square10 + Square11 + Square12 + Square13 
  + Square14 + Square15

  row = Square0->0 + Square1->0 + Square2->0 + Square3->0 + 
        Square4->1 + Square5->1 + Square6->1 + Square7->1 + 
        Square8->2 + Square9->2 + Square10->2 + Square11->2 + 
        Square12->3 + Square13->3 + Square14->3 + Square15->3

  col = Square0->0 + Square1->1 + Square2->2 + Square3->3 + 
        Square4->0 + Square5->1 + Square6->2 + Square7->3 + 
        Square8->0 + Square9->1 + Square10->2 + Square11->3 + 
        Square12->0 + Square13->1 + Square14->2 + Square15->3

  connections = Square0->(Square1 + Square4) + 
      Square1->(Square0 + Square2 + Square5) + 
      Square2->(Square1 + Square3) + 
      Square3->(Square2 + Square7) + 
      Square4->(Square0 + Square5 + Square8) + 
      Square5->(Square1 + Square4 + Square6 + Square9) + 
      Square6->(Square5) +
      Square7->(Square3 + Square11) + 
      Square8->(Square4 + Square9 + Square12) + 
      Square9->(Square5 + Square8 + Square10 + Square13) + 
      Square10->(Square9 + Square11 + Square14) +
      Square11->(Square7 + Square10 + Square15) + 
      Square12->(Square13 + Square8) + 
      Square13->(Square9 + Square12 + Square14) +
      Square14->(Square10 + Square13 + Square15) +
      Square15->(Square11 + Square14)

  Theseus = Theseus0
  Minotaur = Minotaur0
 
  Game = Game0
  Exit = Exit0
  Player = Minotaur0 + Theseus0
}

test expect {
  mazeWithFakeOutWinnable: {
    tracesWithWin
    sum[Theseus.location.row] = 0
    sum[Theseus.location.col] = 2
    sum[Minotaur.location.row] = 2
    sum[Minotaur.location.col] = 0
  } for 16 Square, exactly 5 Int for mazeWithFakeOut is sat

  mazeWithFakeOutCannotFollowSimpleStrategy: {
    tracesWithTheseusMoveToExit
    eventually win
    sum[Theseus.location.row] = 0
    sum[Theseus.location.col] = 2
    sum[Minotaur.location.row] = 2
    sum[Minotaur.location.col] = 0
  } for 16 Square, exactly 5 Int for mazeWithFakeOut is unsat
}

inst mazeGuaranteedLose {
   /*
  Minotaur at column 1 row 2. Theseus at column 0, row 3
  E: Exit
   _ _ _ _
  |_   _| |
  |       |
  | |M    |
  |T _|_|E|
  */
  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + Square6 + 
          Square7 + Square8 + Square9 + Square10 + Square11 + Square12 + Square13 + Square14 + Square15

  Minotaur = Minotaur0
  MinotaurTurn1 = MinotaurTurn10
  MinotaurTurn2 = MinotaurTurn20
  Theseus = Theseus0

  Exit = Exit0
  TheseusTurn = TheseusTurn0
  Game = Game0

  Player = Minotaur0 + Theseus0
  PossibleTurn = MinotaurTurn10 + MinotaurTurn20 + TheseusTurn0

  connections = Square0->Square1 + Square0->Square2 + Square0->Square4 + 
                Square1->Square0 + Square1->Square3 + Square1->Square7 + 
                Square2->Square0 + Square3->Square1 + Square4->Square0 + 
                Square4->Square5 + Square4->Square7 + Square4->Square10 + 
                Square5->Square4 + Square6->Square8 + Square7->Square1 + 
                Square7->Square4 + Square7->Square11 + Square8->Square6 + 
                Square8->Square11 + Square8->Square12 + Square9->Square10 + 
                Square9->Square15 + Square10->Square4 + Square10->Square9 + 
                Square10->Square11 + Square11->Square7 + Square11->Square8 + 
                Square11->Square10 + Square11->Square14 + Square12->Square8 + 
                Square13->Square14 + Square13->Square15 + Square14->Square11 + 
                Square14->Square13 + Square15->Square9 + Square15->Square13

  row = Square0->2 + Square1->1 + Square2->3 + Square3->0 + Square4->2 + 
        Square5->3 + Square6->0 + Square7->1 + Square8->0 + Square9->3 + 
        Square10->2 + Square11->1 + Square12->0 + Square13->2 + Square14->1 + Square15->3
  
  col = Square0->3 + Square1->3 + Square2->3 + Square3->3 + Square4->2 + 
        Square5->2 + Square6->2 + Square7->2 + Square8->1 + Square9->1 + 
        Square10->1 + Square11->1 + Square12->0 + Square13->0 + Square14->0 + Square15->0
  
  next = MinotaurTurn10->MinotaurTurn20 + MinotaurTurn20->TheseusTurn0 + TheseusTurn0->MinotaurTurn10
  location = Theseus0->Square15 + Minotaur0->Square10
  position = Exit0->Square2
  turn = Game0->TheseusTurn0
}


// Show that this maze has no solutions where Theseus wins
test expect {
  theseusTrapped: {
    tracesWithWin
    sum[Theseus.location.row] = 3
    sum[Theseus.location.col] = 0
    sum[Minotaur.location.row] = 2
    sum[Minotaur.location.col] = 1
  } for 16 Square, exactly 5 Int for mazeGuaranteedLose is unsat 

  theseusTrappedWithoutStrat: {
    traces
    sum[Theseus.location.row] = 3
    sum[Theseus.location.col] = 0
    sum[Minotaur.location.row] = 2
    sum[Minotaur.location.col] = 1
  } for 16 Square, exactly 5 Int for mazeGuaranteedLose is unsat 
}

--================================== TESTS ==================================--

--============================== general cases ==============================--

test expect {
  vacuityTraces: {
    traces
  } for 16 Square, exactly 5 Int is sat

  vacuityWin: {
    tracesWithWin
  } for 16 Square, exactly 5 Int is sat

  vacuityLose: {
    tracesWithLose
  } for 16 Square, exactly 5 Int is sat
}

inst basicMaze {
  /*
  E: Exit
   _ _ _ _
  |       |
  |       |
  |  _ _  |
  |_ _ _|E|
  */

  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + Square6 
  + Square7 + Square8 + Square9 + Square10 + Square11 + Square12 + Square13 
  + Square14 + Square15

  row = Square0->0 + Square1->0 + Square2->0 + Square3->0 + 
        Square4->1 + Square5->1 + Square6->1 + Square7->1 + 
        Square8->2 + Square9->2 + Square10->2 + Square11->2 + 
        Square12->3 + Square13->3 + Square14->3 + Square15->3

  col = Square0->0 + Square1->1 + Square2->2 + Square3->3 + 
        Square4->0 + Square5->1 + Square6->2 + Square7->3 + 
        Square8->0 + Square9->1 + Square10->2 + Square11->3 + 
        Square12->0 + Square13->1 + Square14->2 + Square15->3

  connections = Square0->(Square1 + Square4) + 
      Square1->(Square0 + Square2 + Square5) + 
      Square2->(Square1 + Square6 + Square3) + 
      Square3->(Square2 + Square7) + 
      Square4->(Square0 + Square5 + Square8) + 
      Square5->(Square1 + Square4 + Square6 + Square9) + 
      Square6->(Square2 + Square5 + Square7 + Square10) +
      Square7->(Square3 + Square6 + Square11) + 
      Square8->(Square4 + Square9 + Square12) + 
      Square9->(Square5 + Square8 + Square10) + 
      Square10->(Square6 + Square9 + Square11) +
      Square11->(Square7 + Square10 + Square15) + 
      Square12->(Square13 + Square8) + 
      Square13->(Square12 + Square14) +
      Square14->(Square13) +
      Square15->(Square11)

  Theseus = Theseus0
  Minotaur = Minotaur0

  Game = Game0
  Exit = Exit0
  Player = Minotaur0 + Theseus0

}


test expect {
  /*
  E: Exit
  M: Minotaur
  T: Theseus
   _ _ _ _
  |       |
  |    T  |
  |  _ _  |
  |_ _ M|E|
  */
  canWinTest: {
    tracesWithWin
    sum[Theseus.location.row] = 1
    sum[Theseus.location.col] = 2
    sum[Minotaur.location.row] = 3
    sum[Minotaur.location.col] = 2
  } for 16 Square, exactly 5 Int for basicMaze is sat 

  /*
  E: Exit
  M: Minotaur
  T: Theseus
   _ _ _ _
  |       |
  |    M  |
  |  _ _  |
  |_ _ T|E|

  */
  mustLoseTest1: {
    tracesWithWin
    sum[Minotaur.location.row] = 1
    sum[Minotaur.location.col] = 2
    sum[Theseus.location.row] = 3
    sum[Theseus.location.col] = 2
  } for 16 Square, exactly 5 Int for basicMaze is unsat 

  mustLoseTest2: {
    tracesWithLose
    sum[Minotaur.location.row] = 1
    sum[Minotaur.location.col] = 2
    sum[Theseus.location.row] = 3
    sum[Theseus.location.col] = 2
  } for 16 Square, exactly 5 Int for basicMaze is sat 
}


inst interestingMaze {
  /*
  E: Exit
   _ _ _ _
  |    _ _|
  | |     |
  |_| |_| |
  |_ _ _ E|
  */

  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + 
      Square6 + Square7 + Square8 + Square9 + Square10 + Square11 + 
      Square12 + Square13 + Square14 + Square15
  
  row = Square0->0 + Square1->1 + Square2->2 + Square3->3 + Square4->1 + 
      Square5->3 + Square6->2 + Square7->0 + Square8->0 + Square9->1 + 
      Square10->2 + Square11->3 + Square12->3 + Square13->1 + Square14->0 + 
      Square15->2
  col = Square0->3 + Square1->3 + Square2->3 + Square3->3 + Square4->2 + 
      Square5->2 + Square6->2 + Square7->2 + Square8->1 + Square9->1 + 
      Square10->1 + Square11->1 + Square12->0 + Square13->0 + Square14->0 + 
      Square15->0

  connections = Square0->Square7 + Square1->Square2 + Square1->Square4 + 
      Square2->Square1 + Square2->Square3 + Square3->Square2 + 
      Square3->Square5 + Square4->Square1 + Square4->Square6 + 
      Square4->Square9 + Square5->Square3 + Square5->Square11 + 
      Square6->Square4 + Square7->Square0 + Square7->Square8 + 
      Square8->Square7 + Square8->Square9 + Square8->Square14 + 
      Square9->Square4 + Square9->Square8 + Square9->Square10 + 
      Square10->Square9 + Square10->Square11 + Square11->Square5 + 
      Square11->Square10 + Square11->Square12 + Square12->Square11 + 
      Square13->Square14 + Square13->Square15 + Square14->Square8 + 
      Square14->Square13 + Square15->Square13

  Minotaur = Minotaur0
  Theseus = Theseus0
  Game = Game0
  Player = Minotaur0 + Theseus0
}

test expect {
  theseusWinTest: {
    tracesWithWin
    sum[Theseus.location.row] = 1
    sum[Theseus.location.col] = 3
    sum[Minotaur.location.row] = 1
    sum[Minotaur.location.col] = 2
  } for 16 Square, exactly 5 Int for interestingMaze is unsat 
}

// NOTE: Maybe add other interesting examples with this maze?

--============================= validConnections =============================--

inst validConnectionsExample {
  connections = Square0->Square1 + Square1->Square0 + Square1->Square6 
  + Square2->Square4 + Square3->Square7 + Square4->Square2 + Square4->Square5 
  + Square4->Square9 + Square5->Square4 + Square5->Square6 + Square5->Square10 
  + Square6->Square1 + Square6->Square5 + Square6->Square7 + Square7->Square3 
  + Square7->Square6 + Square7->Square8 + Square8->Square7 + Square8->Square11 
  + Square8->Square14 + Square9->Square4 + Square9->Square10 + Square9->Square12 
  + Square10->Square5 + Square10->Square9 + Square11->Square8 + Square11->Square15 
  + Square12->Square9 + Square12->Square13 + Square13->Square12 + Square14->Square8 
  + Square15->Square11
}

inst connectionTwoHopsAway {
  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + Square6 
  + Square7 + Square8 + Square9 + Square10 + Square11 + Square12 + Square13 
  + Square14 + Square15

  row = Square0->2 + Square1->1 + Square2->3 + Square3->0 + Square4->3 
  + Square5->2 + Square6->1 + Square7->0 + Square8->0 + Square9->3 
  + Square10->2 + Square11->1 + Square12->3 + Square13->2 + Square14->0 + Square15->1

  col = Square0->3 + Square1->3 + Square2->3 + Square3->3 + Square4->2 
  + Square5->2 + Square6->2 + Square7->2 + Square8->1 + Square9->1 
  + Square10->1 + Square11->1 + Square12->0 + Square13->0 + Square14->0 + Square15->0

  connections = Square0->Square1 + Square1->Square0 + Square1->Square6 
  + Square2->Square4 + Square3->Square7 + Square4->Square2 + Square4->Square5 
  + Square4->Square9 + Square5->Square4 + Square5->Square6 + Square5->Square10 
  + Square6->Square1 + Square6->Square5 + Square6->Square7 + Square7->Square3 
  + Square7->Square6 + Square7->Square8 + Square8->Square7 + Square8->Square11 
  + Square8->Square14 + Square9->Square4 + Square9->Square10 + Square9->Square12 
  + Square10->Square5 + Square10->Square9 + Square11->Square8 + Square11->Square15 
  + Square12->Square9 + Square12->Square13 + Square13->Square12 + Square14->Square8 
  + Square15->Square11 + Square14->Square7 + Square7->Square14
}

test expect {
  pathBetweenAllPairsOfSquares: {
    validConnections => {
      all sq1, sq2: Square | sq2 in sq1.^connections
    }
  } for 16 Square, exactly 5 Int is theorem

  symmetricConnections: {
    validConnections => { connections = ~connections }
  } for 16 Square, exactly 5 Int is theorem

  nonreflexiveConnections: {
    validConnections => { no iden & connections }
  } for 16 Square, exactly 5 Int is theorem

  validConnectionsExampleTest: {
    validConnections
  } for 16 Square, exactly 5 Int for validConnectionsExample is sat

  connectionTwoHopsAwayTest: {
    validConnections
  } for 16 Square, exactly 5 Int for connectionTwoHopsAway is unsat
}

--================================ validGame ================================--
inst validGameExample {
  Theseus = Theseus0
  Minotaur = Minotaur0

  Game = Game0
  Exit = Exit0
  Player = Minotaur0 + Theseus0

  TheseusTurn = TheseusTurn0
  MinotaurTurn1 = MinotaurTurn10
  MinotaurTurn2 = MinotaurTurn20
  PossibleTurn = MinotaurTurn10 + MinotaurTurn20 + TheseusTurn0
  next = MinotaurTurn10->MinotaurTurn20 + MinotaurTurn20->TheseusTurn0 
  + TheseusTurn0->MinotaurTurn10

  location = Theseus0->Square15 + Minotaur0->Square11
  position = Exit0->Square2
  turn = Game0->MinotaurTurn20

  Square = Square0 + Square1 + Square2 + Square3 + Square4 + Square5 + Square6 
  + Square7 + Square8 + Square9 + Square10 + Square11 + Square12 + Square13 
  + Square14 + Square15

  row = Square0->2 + Square1->1 + Square2->3 + Square3->0 + Square4->3 
  + Square5->2 + Square6->1 + Square7->0 + Square8->0 + Square9->3 
  + Square10->2 + Square11->1 + Square12->3 + Square13->2 + Square14->0 + Square15->1

  col = Square0->3 + Square1->3 + Square2->3 + Square3->3 + Square4->2 
  + Square5->2 + Square6->2 + Square7->2 + Square8->1 + Square9->1 
  + Square10->1 + Square11->1 + Square12->0 + Square13->0 + Square14->0 + Square15->0
  
  connections = Square0->Square1 + Square1->Square0 + Square1->Square6 
  + Square2->Square4 + Square3->Square7 + Square4->Square2 + Square4->Square5 
  + Square4->Square9 + Square5->Square4 + Square5->Square6 + Square5->Square10 
  + Square6->Square1 + Square6->Square5 + Square6->Square7 + Square7->Square3 
  + Square7->Square6 + Square7->Square8 + Square8->Square7 + Square8->Square11 
  + Square8->Square14 + Square9->Square4 + Square9->Square10 + Square9->Square12 
  + Square10->Square5 + Square10->Square9 + Square11->Square8 + Square11->Square15 
  + Square12->Square9 + Square12->Square13 + Square13->Square12 + Square14->Square8 
  + Square15->Square11
}

test expect {
  validGameExampleTest: { 
    validGame 
  } for 16 Square, exactly 5 Int for validGameExample is sat 
}
