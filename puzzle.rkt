#lang forge

option problem_type temporal

abstract sig Player {
  var location: one Square
}

one sig Theseus extends Player {}
one sig Minotaur extends Player {}

one sig Game { 
  var turn: one Player 
}

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

pred validMaze {
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

run validMaze for 16 Square, exactly 5 Int

pred init{
  -- constrain initial theseus position

  -- constrain initial minotaur position
}

pred doNothing {
  position' = position
  turn' != turn
}

pred theseusMove {
  -- preconditions
  Theseus in Game.turn 

  doNothing

}

pred minotaurMove {
  -- preconditions
  Minotaur in Game.turn

  doNothing
}

pred win {
  Theseus.location in Exit.position
  always doNothing
}

pred lose {
  Minotaur.location in Theseus.location
  always doNothing
}

pred traces {
  validMaze
  init
  always (theseusMove or minotaurMove) or win or lose
}