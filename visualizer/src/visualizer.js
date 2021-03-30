const MAZE_WIDTH = 4;
const MAZE_HEIGHT = 4;

let StateControls = ({ currentTrace, setCurrentTrace }) => {
  return (
    <div>
      <button onClick={() => setCurrentTrace(currentTrace - 1)}>
        Previous Trace
      </button>
      Current Trace: {currentTrace}
      <button onClick={() => setCurrentTrace(currentTrace + 1)}>
        Next Trace
      </button>
    </div>
  );
};

let Maze = ({ currentTrace, mazeLayout }) => {
  return <div></div>;
};

let App = ({ mazeLayout }) => {
  let [currentTrace, setCurrentTrace] = useState(0);
  return (
    <div>
      <StateControls
        currentTrace={currentTrace}
        setCurrentTrace={setCurrentTrace}
      />
      <Maze currentTrace={currentTrace} mazeLayout={mazeLayout} />{" "}
    </div>
  );
};

/**
 * Function to convert forge integer tuples to javascript integers
 * @param {AlloyTuple} forgeInt
 * @returns integer
 */
const forgeIntToJsInt = (forgeInt) => forgeInt.atoms()[0].id();

const main = () => {
  // Make a 2d array that will have MAZE_WIDTH cols and MAZE_HEIGHT rows
  let mazeLayout = [];
  for (let i = 0; i < MAZE_HEIGHT; i++) {
    mazeLayout.append(Array(MAZE_WIDTH));
  }
  for (const square of Square.atoms()) {
    let r = forgeIntToJsInt(square.join(row));
    let c = forgeIntToJsInt(square.join(col));
    mazeLayout[r][c] = square;
  }

  const container = document.querySelector(".script-stage").children[0];
  ReactDOM.render(<App mazeLayout={mazeLayout} />, container);
};
main();
