import * as d3 from "d3";

const MAZE_WIDTH = 4;
const MAZE_HEIGHT = 4;

const SQUARE_SIZE = "70px";
const BORDER_STYLE = "2px solid black";

const THESEUS_IMG = "https://files.paulbiberstein.me/theseus.png";
const MINOTAUR_IMG = "https://files.paulbiberstein.me/minotaur.png";
const EXIT_IMG =
  "http://www.slate.com/content/dam/slate/archive/2010/03/1_123125_2245632_2246167_2247195_100308_signs_exit_greentn.jpg";

let DO_DRAW_INDICES = false;
let DO_DRAW_THESEUS_DISTANCE = false;

const SELECTED_INSTANCE = 0;

/**
 * Function to convert forge integer tuples to javascript integers
 * @param {AlloyTuple} forgeInt
 * @returns integer
 */
const forgeIntToJsInt = (forgeInt) => forgeInt.atoms()[0].id();

/**
 * Computer the manhattan distance between two coords
 * @param {number} r1 row of first square
 * @param {number} c1 col of first square
 * @param {number} r2 row of second square
 * @param {number} c2 col of second square
 * @returns (number) the taxicab distance between the two squares
 */
const manhattanDistance = (r1, c1, r2, c2) =>
  Math.abs(r1 - r2) + Math.abs(c1 - c2);

const getRowAndCol = (square) => [
  square.join(row).tuples()[0].atoms()[0].id(),
  square.join(col).tuples()[0].atoms()[0].id(),
];

/**
 * Queries the current turn and returns an image url corresponding
 * to the character whose turn it currently is
 * @returns the url of the correct image
 */
const getImgForCurrentTurn = () =>
  Game.turn.id().substr(0, 8) == "Minotaur" ? MINOTAUR_IMG : THESEUS_IMG;

/**
 * Computer which walls exist around a given square.
 * @param {number} r the row
 * @param {number} c the column
 * @param {number[][]} mazeLayout two dimensional array to resolve coordinates to Forge atoms
 * @returns a four element array of 1 or 0 that represents the squares walls
 */
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

/**
 * Appends an image tag with the specified image to the specified div
 * @param {string} divSelector
 * @param {string} imageSrc
 */
const appendImgToDiv = (divSelector, imageSrc) => {
  d3.select(divSelector)
    .append("img")
    .style("position", "absolute")
    .style("bottom", "0px")
    .style("right", "0px")
    .style("height", "50px")
    .style("width", "auto")
    .attr("src", imageSrc);
};

/**
 * The main draw function for the visualizer
 * @param {number[][]} mazeLayout two dimensional array to resolve coordinates to Forge atoms
 */
const draw = (mazeLayout) => {
  // Clear container before drawing
  d3.select(div).html("");

  // Adjust the container so that our visualization is centered
  d3.select(div)
    .style("display", "flex")
    .style("flex-direction", "column")
    .style("align-items", "center")
    .style("justify-content", "center");

  drawInterface(mazeLayout);
  drawMaze(mazeLayout);
};

/**
 * Draw the interface components of the visualizer
 */
const drawInterface = (mazeLayout) => {
  const container = d3.select(div).append("div").style("min-width", "300px");

  // Add current turn
  container
    .append("div")
    .attr("id", "current-turn")
    .style("border", "1px solid black")
    .style("padding", "3px")
    .append("h2")
    .text("Current Turn");
  d3.select("#current-turn")
    .append("img")
    .attr("src", getImgForCurrentTurn())
    .style("height", "40px");

  // Add options
  container
    .append("div")
    .attr("id", "options")
    .style("border", "1px solid black")
    .style("padding", "3px")
    .append("h2")
    .text("Options");
  // Draw draw_ids checkbox
  d3.select("#options")
    .append("input")
    .attr("type", "checkbox")
    .attr("id", "draw_ids")
    .attr("name", "draw_ids")
    .style("margin", ".4rem")
    .attr(DO_DRAW_INDICES ? "checked" : "data-dummy", "")
    .on("change", () => {
      DO_DRAW_INDICES = !DO_DRAW_INDICES;
      draw(mazeLayout);
    });
  d3.select("#options")
    .append("label")
    .attr("for", "draw_ids")
    .text("Draw square indices");

  d3.select("#options").append("br");

  // Draw draw_theseus_dist checkbox
  d3.select("#options")
    .append("input")
    .attr("type", "checkbox")
    .attr("id", "draw_theseus_dist")
    .attr("name", "draw_theseus_dist")
    .style("margin", ".4rem")
    .attr(DO_DRAW_THESEUS_DISTANCE ? "checked" : "data-dummy", "")
    .on("change", () => {
      DO_DRAW_THESEUS_DISTANCE = !DO_DRAW_THESEUS_DISTANCE;
      draw(mazeLayout);
    });
  d3.select("#options")
    .append("label")
    .attr("for", "draw_theseus_dist")
    .text("Draw distance from Theseus");
};

/**
 * Draw the maze
 * @param {number[][]} mazeLayout
 */
const drawMaze = (mazeLayout) => {
  // figure out the row and col of the square that theseus, the minotaur, and the exit are at.
  const [theseusRow, theseusCol] = getRowAndCol(Theseus.join(location));
  const [minotaurRow, minotaurCol] = getRowAndCol(Minotaur.join(location));
  const [exitRow, exitCol] = getRowAndCol(Exit.join(position));

  // Create the container to hold the maze
  let mazeContainer = d3
    .select(div)
    .append("div")
    .attr("id", "maze")
    .style("border", "8px ridge #e1b31e");

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
      const walls = findWalls(r, c, mazeLayout);

      // Create a `div` for this container and style it
      d3.select(`#maze-row-${r}`)
        .append("div")
        .attr("id", `maze-square-${r}${c}`)
        .style("position", "relative")
        .style("width", SQUARE_SIZE)
        .style("height", SQUARE_SIZE)
        .style("background-color", "lightgrey")
        .style("border-top", walls[0] ? BORDER_STYLE : "")
        .style("border-right", walls[1] ? BORDER_STYLE : "")
        .style("border-bottom", walls[2] ? BORDER_STYLE : "")
        .style("border-left", walls[3] ? BORDER_STYLE : "");
      // Draw square row and column as text
      if (DO_DRAW_INDICES) {
        d3.select(`#maze-square-${r}${c}`)
          .append("div")
          .style("margin", "2px")
          .text(`${r},${c}`);
      }

      // Draw distance to theseus
      if (DO_DRAW_THESEUS_DISTANCE) {
        const dist = manhattanDistance(r, c, theseusRow, theseusCol);
        d3.select(`#maze-square-${r}${c}`)
          .append("div")
          .style("margin", "2px")
          .text(dist);
      }

      // if the exit is at this location, add a dot
      if (r == exitRow && c == exitCol) {
        appendImgToDiv(`#maze-square-${r}${c}`, EXIT_IMG);
      }
      // If theseus is at this location, add a dot
      if (r == theseusRow && c == theseusCol) {
        appendImgToDiv(`#maze-square-${r}${c}`, THESEUS_IMG);
      }
      // If the minotaur is at this location, add a dot
      if (r == minotaurRow && c == minotaurCol) {
        appendImgToDiv(`#maze-square-${r}${c}`, MINOTAUR_IMG);
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

  draw(mazeLayout);
};

main();
