#lang forge

option problem_type temporal
option max_tracelength 14

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

  -- ideas for walls
  -- specify explicitly where walls should exist/how many
  -- constrain num connections per square

  -- no sq: Square | #sq.connections = 3
}

pred validGame {
  -- Setup turn order
  next = MinotaurTurn1->MinotaurTurn2 + MinotaurTurn2->TheseusTurn + TheseusTurn->MinotaurTurn1

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

// run validGame for 16 Square, exactly 5 Int

pred init{
  -- constrain initial theseus position
  Theseus.location != Exit.position
  
  -- constrain initial minotaur position
  Minotaur.location != Theseus.location

  -- theseus moves first
  Game.turn = TheseusTurn
}

pred doNothing {
  location' = location
}

pred moveLeft[p : Player] {
  p.location.col != sing[0]
  
  some sq : Square | {
    -- Required indices
    sq.col = sing[subtract[sum[(p.location).col], 1]]
    sq.row = p.location.row

    -- Must be able to move from current square to the left
    sq in (p.location).connections
  }
  (p.location').col = sing[subtract[sum[p.location.col], 1]]
  (p.location').row = p.location.row
}

pred moveRight[p : Player] {
  p.location.col != sing[3]
  
  some sq : Square | {
    -- Required indices
    sq.col = sing[add[sum[(p.location).col], 1]]
    sq.row = p.location.row

    -- Must be able to move from current square to the right
    sq in (p.location).connections
  }
  (p.location').col = sing[add[sum[p.location.col], 1]]
  (p.location').row = p.location.row
}

pred moveDown[p : Player] {
  p.location.row != sing[3]
  
  some sq : Square | {
    -- Required indices
    sq.row = sing[add[sum[(p.location).row], 1]]
    sq.col = p.location.col

    -- Must be able to move from current square to below
    sq in (p.location).connections
  }
  (p.location').row = sing[add[sum[p.location.row], 1]]
  (p.location').col = p.location.col
}

pred moveUp[p : Player] {
  p.location.row != sing[0]
  
  some sq : Square | {
    -- Required indices
    sq.row = sing[subtract[sum[(p.location).row], 1]]
    sq.col = p.location.col

    -- Must be able to move from current square to above
    sq in (p.location).connections
  }
  (p.location').row = sing[subtract[sum[p.location.row], 1]]
  (p.location').col = p.location.col
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

fun getDist[s1: Square, s2: Square]: Int {
  sing[add[abs[subtract[sum[s1.row], sum[s2.row]]], abs[subtract[sum[s1.col], sum[s2.col]]]]]
}

pred closerToTheseus[start: Square, end: Square] {
  sum[getDist[start, Theseus.location]] > sum[getDist[end, Theseus.location]]
}

pred minotaurMove {
  -- Theseus doesn't move
  Theseus.location = Theseus.(location')
  
  { some sq: (Minotaur.location).connections | { closerToTheseus[Minotaur.location, sq] }} => {
    (Minotaur.(location')) in (Minotaur.location).connections
    closerToTheseus[Minotaur.location, Minotaur.(location')]
  } else {
    doNothing
  }
}

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

// run {
//   validGame 
//   init
//   theseusMove
//   eventually (win)
// } for 16 Square, exactly 5 Int

pred tracesWithWin {
  traces
  eventually win
}

pred tracesWithLose {
  traces
  eventually lose
}

pred interesting {
  -- Ensure that theseus starts at least 2 from the exist
  sum[getDist[Theseus.location, Exit.position]] > 2

}

run {
  tracesWithWin
  interesting
} for 16 Square, exactly 5 Int, exactly 3 PossibleTurn