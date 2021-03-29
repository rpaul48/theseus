let StateControls = () => {
  return <></>;
};

let Maze = () => {
  return <></>;
};

let App = () => {
  let [currentTrace, setCurrentTrace] = useState(0);
  return (
    <>
      <StateControls
        currentTrace={currentTrace}
        setCurrentTrace={setCurrentTrace}
      />
      <Maze currentTrace={currentTrace} />{" "}
    </>
  );
};

const container = document.querySelector(".script-stage").children[0];
ReactDOM.render(<App />, container);
