const MAZE_WIDTH = 4;
const MAZE_HEIGHT = 4;

const SQUARE_SIZE = "70px";
const BORDER_STYLE = "2px solid black";

const ANIM_DURATION = 500;

const THESEUS_IMG = "https://files.paulbiberstein.me/theseus.png";
const MINOTAUR_IMG = "https://files.paulbiberstein.me/minotaur.png";
const EXIT_IMG =
  "http://www.slate.com/content/dam/slate/archive/2010/03/1_123125_2245632_2246167_2247195_100308_signs_exit_greentn.jpg";
const DENY_IMG =
  "https://upload.wikimedia.org/wikipedia/commons/thumb/3/31/ProhibitionSign2.svg/1200px-ProhibitionSign2.svg.png";
const CONGRATULATIONS_IMG =
  "https://lh3.googleusercontent.com/proxy/u5lNdSSWlA5pqSrtfVwJ9_t2_g5vwweA4syddDj-WbUDFdCA-Cu_JMP04vbehLoYBIzcaI8qbMVnxM63QJItswP9Wcgrk-muwZtruJ7yDjBRi-1IGc9Z9_-o1Q";

let DO_DRAW_INDICES = false;
let DO_DRAW_THESEUS_DISTANCE = false;

// Instead of relying on Sterling to track the current instance of the trace,
// we'll manually track it here instead
let SELECTED_INSTANCE = 0;

/**
 * This is equal to the lower of the max instance or the instance where theseus wins.
 * It's set in first time initialization
 */
let MAX_INSTANCE_INDEX = instances.length - 1;

/**
 * This function wraps all relation accesses behind a function so we can manually control the selected instance
 * @param {string} relName
 */
const getRelation = (relName, instance_index) => {
  // If an instance isn't supplied then use the current index
  if (instance_index === undefined) {
    instance_index = SELECTED_INSTANCE;
  }
  if (
    ![
      "position",
      "row",
      "location",
      "turn",
      "next",
      "connections",
      "col",
    ].includes(relName)
  ) {
    console.error("Tried to get non-existent relation");
  }
  return instances[instance_index].field(relName);
};

/**
 * This function wraps all sig accesses behind a function so we can manually control the selected instance
 * @param {string} sigName
 */
const getSig = (sigName, instance_index) => {
  // If an instance isn't supplied then use the current index
  if (instance_index === undefined) {
    instance_index = SELECTED_INSTANCE;
  }
  if (
    ![
      "Int",
      "univ",
      "Player",
      "Minotaur",
      "PossibleTurn",
      "MinotaurTurn1",
      "Theseus",
      "Exit",
      "MinotaurTurn2",
      "TheseusTurn",
      "Game",
      "Square",
    ].includes(sigName)
  ) {
    console.error("Tried to get non-existent sig");
  }
  return instances[instance_index].signature(sigName);
};

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

/**
 * Gets the row and column for a given square of a given instance
 * @param {AlloyAtom} square the square atom
 * @param {number} inst instance to check. Defaults to selected instance
 * @returns 2-tuple of row and col
 */
const getRowAndCol = (square, inst) => {
  if (inst === undefined) {
    inst = SELECTED_INSTANCE;
  }
  return [
    square.join(getRelation("row", inst)).tuples()[0].atoms()[0].id(),
    square.join(getRelation("col", inst)).tuples()[0].atoms()[0].id(),
  ];
};

/**
 * Queries the current turn and returns an image url corresponding
 * to the character whose turn it currently is
 * @returns the url of the correct image
 */
const getImgForCurrentTurn = () => {
  return getSig("Game")
    .join(getRelation("turn"))
    .tuples()[0]
    .atoms()[0]
    .id()
    .substr(0, 8) == "Minotaur"
    ? MINOTAUR_IMG
    : THESEUS_IMG;
};

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
    .join(getRelation("connections"))
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
const appendImgToDiv = (divSelector, imageSrc, id) => {
  d3.select(divSelector)
    .append("img")
    .attr("id", id)
    .style("position", "absolute")
    .style("bottom", "0px")
    .style("right", "0px")
    .style("height", "50px")
    .style("width", "auto")
    .style("z-index", id === "exit-img" ? "9" : "10")
    .attr("src", imageSrc);
};

/**
 * Creates a 2d array of "square" atoms that accurately reflects "row" and "col" relations
 * @returns 2d array of "square" atoms
 */
const getMazeLayout = () => {
  // Make a 2d array that will have MAZE_WIDTH cols and MAZE_HEIGHT rows
  let mazeLayout = [];
  for (let i = 0; i < MAZE_HEIGHT; i++) {
    mazeLayout.push(Array(MAZE_WIDTH));
  }
  for (const square of getSig("Square").atoms()) {
    let r = forgeIntToJsInt(square.join(getRelation("row")).tuples()[0]);
    let c = forgeIntToJsInt(square.join(getRelation("col")).tuples()[0]);
    mazeLayout[r][c] = square;
  }

  return mazeLayout;
};

/**
 * Attempts to advance to the next instance (with animation)
 */
const nextInstance = () => {
  if (SELECTED_INSTANCE === MAX_INSTANCE_INDEX) {
    return;
  }

  // Figure out whose turn it is to move and get a css selector for their image
  let [sigName, selector] =
    getSig("Game")
      .join(getRelation("turn"))
      .tuples()[0]
      .atoms()[0]
      .id()
      .substr(0, 8) == "Minotaur"
      ? ["Minotaur", "#minotaur-img"]
      : ["Theseus", "#theseus-img"];

  let [currentRow, currentCol] = getRowAndCol(
    getSig(sigName).join(getRelation("location"))
  );

  let [nextRow, nextCol] = getRowAndCol(
    getSig(sigName, SELECTED_INSTANCE + 1).join(
      getRelation("location", SELECTED_INSTANCE + 1)
    ),
    SELECTED_INSTANCE + 1
  );

  // The square size in pixels as an integer
  let square_size_px = parseInt(SQUARE_SIZE.substr(0, SQUARE_SIZE.length - 2));
  // The location change of the characer in pixels
  let [xDelta, yDelta] = [
    (nextCol - currentCol) * square_size_px,
    (nextRow - currentRow) * square_size_px,
  ];

  // Perform the animation
  d3.select(selector)
    .transition()
    .style("right", -xDelta + "px")
    .style("bottom", -yDelta + "px")
    .duration(ANIM_DURATION)
    .ease(d3.easeSinInOut);

  // If the player chose to do nothing then flash a warning symbol
  if (xDelta === 0 && yDelta === 0) {
    d3.select(d3.select(selector).node().parentNode)
      .append("img")
      .style("position", "absolute")
      .style("bottom", "0px")
      .style("right", "0px")
      .style("height", "50px")
      .style("width", "50px")
      .style("z-index", "20")
      .style("opacity", "1")
      .attr("src", DENY_IMG)
      .transition()
      .style("opacity", 0)
      .duration(ANIM_DURATION)
      .ease(d3.easeQuadIn);
  }

  // Disable buttons while animating
  document.getElementById("interface").remove();
  drawInterface(true);

  // Once the animation is finished, change to new instance
  setTimeout(() => {
    SELECTED_INSTANCE += 1;
    main();
  }, ANIM_DURATION);
};

/**
 * Attempts to go to the previous instance
 */
const previousInstance = () => {
  if (SELECTED_INSTANCE === 0) {
    return;
  }

  SELECTED_INSTANCE -= 1;
  main();
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

  drawInterface(false);
  drawMaze(mazeLayout);
  drawCongratulations();
};

/**
 * Draw the interface components of the visualizer
 */
const drawInterface = (buttonsDisabled) => {
  const container = d3
    .select(div)
    .append("div")
    .lower()
    .style("min-width", "300px")
    .attr("id", "interface");

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
      main();
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
      main();
    });
  d3.select("#options")
    .append("label")
    .attr("for", "draw_theseus_dist")
    .text("Draw distance from Theseus");

  // Add instance chooser
  container
    .append("div")
    .attr("id", "instance-chooser")
    .style("border", "1px solid black")
    .style("padding", "3px")
    .append("h2")
    .text("Instance Chooser");

  d3.select("#instance-chooser")
    .append("div")
    .text(`Current Instance: ${SELECTED_INSTANCE}`);
  d3.select("#instance-chooser")
    .append("button")
    .attr("type", "button")
    .attr(buttonsDisabled ? "disabled" : "data-dummy", "")
    .on("click", () => {
      SELECTED_INSTANCE = 0;
      main();
    })
    .text("<<");
  d3.select("#instance-chooser")
    .append("button")
    .attr("type", "button")
    .attr(buttonsDisabled ? "disabled" : "data-dummy", "")
    .on("click", () => {
      previousInstance();
    })
    .text("<");
  d3.select("#instance-chooser")
    .append("button")
    .attr("type", "button")
    .attr(buttonsDisabled ? "disabled" : "data-dummy", "")
    .on("click", () => {
      nextInstance();
    })
    .text(">");
  d3.select("#instance-chooser")
    .append("button")
    .attr("type", "button")
    .attr(buttonsDisabled ? "disabled" : "data-dummy", "")
    .on("click", () => {
      SELECTED_INSTANCE = MAX_INSTANCE_INDEX;
      main();
    })
    .text(">>");
};

/**
 * Draw the maze
 * @param {number[][]} mazeLayout
 */
const drawMaze = (mazeLayout) => {
  // figure out the row and col of the square that theseus, the minotaur, and the exit are at.
  const [theseusRow, theseusCol] = getRowAndCol(
    getSig("Theseus").join(getRelation("location"))
  );
  const [minotaurRow, minotaurCol] = getRowAndCol(
    getSig("Minotaur").join(getRelation("location"))
  );
  const [exitRow, exitCol] = getRowAndCol(
    getSig("Exit").join(getRelation("position"))
  );

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
        appendImgToDiv(`#maze-square-${r}${c}`, EXIT_IMG, "exit-img");
      }
      // If theseus is at this location, add a dot
      if (r == theseusRow && c == theseusCol) {
        appendImgToDiv(`#maze-square-${r}${c}`, THESEUS_IMG, "theseus-img");
      }
      // If the minotaur is at this location, add a dot
      if (r == minotaurRow && c == minotaurCol) {
        appendImgToDiv(`#maze-square-${r}${c}`, MINOTAUR_IMG, "minotaur-img");
      }
    }
  }
};

/**
 * Draw the congratulations sticker if the instance is a win
 */
const drawCongratulations = () => {
  const [theseusRow, theseusCol] = getRowAndCol(
    getSig("Theseus").join(getRelation("location"))
  );
  const [exitRow, exitCol] = getRowAndCol(
    getSig("Exit").join(getRelation("position"))
  );

  if (theseusRow === exitRow && theseusCol === exitCol) {
    d3.select(div)
      .append("div")
      .attr("id", "banner-container")
      .style("position", "relative")
      .style("width", "100%")
      .style("display", "flex")
      .style("flex-direction", "column")
      .style("align-items", "center")
      .style("justify-content", "center")
      .append("img")
      .attr("id", "congratulations-banner")
      .attr("src", CONGRATULATIONS_IMG)
      .style("position", "absolute")
      .style("top", "50px")
      .style("width", "100px")
      .style("height", "auto")
      .style("z-index", "30")
      .transition()
      .style("top", "-300px")
      .style("width", "300px")
      .ease(d3.easeBounceOut)
      .duration(1000);
  }
};

/**
 * Call this function to recompute values and redraw the board for the currently SELECTED_INSTANCE
 */
const main = () => {
  let mazeLayout = getMazeLayout();
  draw(mazeLayout);
};

/**
 * This function is called once when the visualizer starts up
 */
const firstTimeInitialization = () => {
  // Compute what instance theseus wins at and track in global variable
  for (let i = 0; i < instances.length; i++) {
    const [theseusRow, theseusCol] = getRowAndCol(
      getSig("Theseus", i).join(getRelation("location", i)),
      i
    );
    const [exitRow, exitCol] = getRowAndCol(
      getSig("Exit", i).join(getRelation("position", i)),
      i
    );

    if (theseusRow === exitRow && theseusCol === exitCol) {
      MAX_INSTANCE_INDEX = i;
      break;
    }
  }

  // Call the main draw function
  main();
};

firstTimeInitialization();
