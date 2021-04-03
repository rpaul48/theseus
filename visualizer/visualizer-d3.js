const MAZE_WIDTH = 4;
const MAZE_HEIGHT = 4;

const SQUARE_SIZE = "70px";
const THESEUS_SIZE = "35px";
const MINOTAUR_SIZE = "30px";
EXIT_SIZE = "25px";
const BORDER_STYLE = "2px solid black";

/**
 * Function to convert forge integer tuples to javascript integers
 * @param {AlloyTuple} forgeInt
 * @returns integer
 */
const forgeIntToJsInt = (forgeInt) => forgeInt.atoms()[0].id();

const findWalls = (r, c, mazeLayout) => {
  square = mazeLayout[r][c];
  const connectedSquares = square
    .join(connections)
    .tuples()
    .map((x) => x.atoms()[0]);

  // Array of walls. Directions are [north, east, south, west]
  const walls = [
    r == 0 || !connectedSquares.includes(mazeLayout[r - 1][c]),
    c == MAZE_WIDTH - 1 || !connectedSquares.includes(mazeLayout[r][c + 1]),
    r == MAZE_HEIGHT - 1 || !connectedSquares.includes(mazeLayout[r + 1][c]),
    c == 0 || !connectedSquares.includes(mazeLayout[r][c - 1]),
  ];
  return walls;
};

const appendDotToDiv = (divSelector, color, size) => {
  d3.select(divSelector)
    .append("div")
    .style("position", "absolute")
    .style("width", size)
    .style("height", size)
    .style("background-color", color)
    .style("border-radius", "100%");
};

const draw = (mazeLayout) => {
  // Adjust the container so that our visualization is centered
  d3.select(div)
    .style("display", "flex")
    .style("flex-direction", "column")
    .style("align-items", "center")
    .style("justify-content", "center");
  // Add instructions
  d3.select(div)
    .append("div")
    .text("Green is Theseus. Red is Minotaur. Blue is exit.");
  d3.select(div).append("div").text(`Current turn: ${Game.turn.id()}`);

  // figure out the name (as a string) of the square that theseus, the minotaur, and the exit are at
  const theseusLocationId = Theseus.join(location).tuples()[0].atoms()[0].id();
  const minotaurLocationId = Minotaur.join(location)
    .tuples()[0]
    .atoms()[0]
    .id();
  const exitLocationId = Exit.join(position).tuples()[0].atoms()[0].id();

  // Create the container to hold the maze
  let mazeContainer = d3.select(div).append("div").attr("id", "maze");

  // Draw each square
  for (let r = 0; r < mazeLayout.length; r++) {
    // Add a container for this row
    mazeContainer
      .append("div")
      .attr("id", `maze-row-${r}`)
      .style("display", "flex")
      .style("flex-direction", "row");
    // Loop through every square in the row
    for (let c = 0; c < mazeLayout[0].length; c++) {
      //Figure out the name (as a string) and the walls for this square
      const square = mazeLayout[r][c];
      const squareId = square.tuples()[0].atoms()[0].id();
      const walls = findWalls(r, c, mazeLayout);

      // Create a `div` for this container and style it
      console.log(`Square at ${squareId}`);
      d3.select(`#maze-row-${r}`)
        .append("div")
        .attr("id", `maze-square-${r}${c}`)
        .style("width", SQUARE_SIZE)
        .style("height", SQUARE_SIZE)
        .style("background-color", "lightgrey")
        .style("border-top", walls[0] ? BORDER_STYLE : "")
        .style("border-right", walls[1] ? BORDER_STYLE : "")
        .style("border-bottom", walls[2] ? BORDER_STYLE : "")
        .style("border-left", walls[3] ? BORDER_STYLE : "")
        .text(`${r},${c}`);

      // If theseus is at this location, add a dot
      if (squareId === theseusLocationId) {
        appendDotToDiv(`#maze-square-${r}${c}`, "green", THESEUS_SIZE);
      }
      // If the minotaur is at this location, add a dot
      if (squareId === minotaurLocationId) {
        appendDotToDiv(`#maze-square-${r}${c}`, "red", MINOTAUR_SIZE);
      }
      // if the exit is at this location, add a dot
      if (squareId === exitLocationId) {
        appendDotToDiv(`#maze-square-${r}${c}`, "blue", EXIT_SIZE);
      }
    }
  }
};

const main = () => {
  // Make a 2d array that will have MAZE_WIDTH cols and MAZE_HEIGHT rows
  let mazeLayout = [];
  for (let i = 0; i < MAZE_HEIGHT; i++) {
    mazeLayout.push(Array(MAZE_WIDTH));
  }
  for (const square of Square.atoms()) {
    let r = forgeIntToJsInt(square.join(row).tuples()[0]);
    let c = forgeIntToJsInt(square.join(col).tuples()[0]);
    mazeLayout[r][c] = square;
  }

  // Clear container before drawing
  d3.select(div).html("");
  draw(mazeLayout);
};
main();
