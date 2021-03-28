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

// run validMaze for 16 Square, exactly 5 Int

pred init{
  -- constrain initial theseus position

  -- constrain initial minotaur position
}

pred doNothing {
  location' = location
  turn' != turn
}

pred theseusMove {
  -- preconditions
  Theseus in Game.turn 

  doNothing

}

// fun getDist[s1: Square, s2: Square]: Int {
//   sing[abs[sum[s1.row] - sum[s2.row]] + abs[sum[s1.col] - sum[s2.col]]]
// }

// fun getCoordDist[x1: Int, x2: Int]: Int {
//   sing[abs[sum[x1.row] - sum[x2.row]]]
// }

pred minotaurMove {
  -- preconditions
  Minotaur in Game.turn

  Theseus.location = Theseus.(location')

  {
    some sq: (Minotaur.location).connections.connections | {
      abs[subtract[sum[sq.row], sum[(Theseus.location).row]]] <= abs[subtract[sum[(Minotaur.location).row], sum[(Theseus.location).row]]]

      abs[subtract[sum[sq.col], sum[(Theseus.location).col]]] <= abs[subtract[sum[(Minotaur.location).col], sum[(Theseus.location).col]]]

      ((abs[subtract[sum[sq.row], sum[(Minotaur.location).row]]] = 2)
      or 
      (abs[subtract[sum[sq.col], sum[(Minotaur.location).col]]] = 2))
    }
  } => {
    (Minotaur.(location')) in (Minotaur.location).connections.connections

    abs[subtract[sum[(Minotaur.(location')).row], sum[(Theseus.location).row]]] <= abs[subtract[sum[(Minotaur.location).row], sum[(Theseus.location).row]]]

    abs[subtract[sum[(Minotaur.(location')).col], sum[(Theseus.location).col]]] <= abs[subtract[sum[(Minotaur.location).col], sum[(Theseus.location).col]]]

    ((abs[subtract[sum[(Minotaur.(location')).row], sum[(Minotaur.location).row]]] = 2)
    or 
    (abs[subtract[sum[(Minotaur.(location')).col], sum[(Minotaur.location).col]]] = 2))

    turn' != turn
  } else {
    doNothing
  }

  // {
  //   {
  //     sum[getCoordDist[Minotaur.location.row, Theseus.location.row]] < 0
  //     some sq: (Minotaur.location).connections.connections | {
  //       sum[sq.row] = sum[sum[Minotaur.location.row], 2]
  //     }
  //   } 
  //   => 
  //   {
  //     sum[(Minotaur.(location')).row] = sum[sum[(Minotaur.(location')).row], 2]
  //     sum[(Minotaur.(location')).col] = sum[(Minotaur.(location')).col]
  //     turn' != turn
  //   }
    
  // }

  // // dist is closer in new location
  // sum[getDist[Minotaur.(location'), Theseus.location]] <= 
  //   sum[getDist[Minotaur.location, Theseus.location]]

  // // moved 2 horizontally or 2 vertically 
  // (
  //   {(abs[sum[(Minotaur.(location')).row] - sum[(Minotaur.location).row]] = 2)
  //   }
  //   or 
  //   (abs[sum[(Minotaur.(location')).col] - sum[(Minotaur.location).col]] = 2)
  //   or 
  //   doNothing
  // )
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

run {
  validMaze
  init
  eventually(minotaurMove) } for 16 Square, exactly 5 Int