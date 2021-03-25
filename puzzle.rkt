#lang forge

option problem_type temporal

abstract sig Player {
  var location: one Square
}

one sig Theseus extends Player {}
one sig Minotaur extends Player {}

sig Square {
  row: one Int,
  col: one Int,
  connections: set Square
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
}

run validMaze for 16 Square, exactly 5 Int

pred init{}


/*





*/