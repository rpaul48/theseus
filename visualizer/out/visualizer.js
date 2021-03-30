var _slicedToArray = function () { function sliceIterator(arr, i) { var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"]) _i["return"](); } finally { if (_d) throw _e; } } return _arr; } return function (arr, i) { if (Array.isArray(arr)) { return arr; } else if (Symbol.iterator in Object(arr)) { return sliceIterator(arr, i); } else { throw new TypeError("Invalid attempt to destructure non-iterable instance"); } }; }();

var MAZE_WIDTH = 4;
var MAZE_HEIGHT = 4;

var StateControls = function StateControls(_ref) {
  var currentTrace = _ref.currentTrace,
      setCurrentTrace = _ref.setCurrentTrace;

  return React.createElement(
    "div",
    null,
    React.createElement(
      "button",
      { onClick: function onClick() {
          return setCurrentTrace(currentTrace - 1);
        } },
      "Previous Trace"
    ),
    "Current Trace: ",
    currentTrace,
    React.createElement(
      "button",
      { onClick: function onClick() {
          return setCurrentTrace(currentTrace + 1);
        } },
      "Next Trace"
    )
  );
};

var Maze = function Maze(_ref2) {
  var currentTrace = _ref2.currentTrace,
      mazeLayout = _ref2.mazeLayout;

  return React.createElement("div", null);
};

var App = function App(_ref3) {
  var mazeLayout = _ref3.mazeLayout;

  var _useState = useState(0),
      _useState2 = _slicedToArray(_useState, 2),
      currentTrace = _useState2[0],
      setCurrentTrace = _useState2[1];

  return React.createElement(
    "div",
    null,
    React.createElement(StateControls, {
      currentTrace: currentTrace,
      setCurrentTrace: setCurrentTrace
    }),
    React.createElement(Maze, { currentTrace: currentTrace, mazeLayout: mazeLayout }),
    " "
  );
};

/**
 * Function to convert forge integer tuples to javascript integers
 * @param {AlloyTuple} forgeInt
 * @returns integer
 */
var forgeIntToJsInt = function forgeIntToJsInt(forgeInt) {
  return forgeInt.atoms()[0].id();
};

var main = function main() {
  // Make a 2d array that will have MAZE_WIDTH cols and MAZE_HEIGHT rows
  var mazeLayout = [];
  for (var i = 0; i < MAZE_HEIGHT; i++) {
    mazeLayout.append(Array(MAZE_WIDTH));
  }
  var _iteratorNormalCompletion = true;
  var _didIteratorError = false;
  var _iteratorError = undefined;

  try {
    for (var _iterator = Square.atoms()[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
      var square = _step.value;

      var r = forgeIntToJsInt(square.join(row));
      var c = forgeIntToJsInt(square.join(col));
      mazeLayout[r][c] = square;
    }
  } catch (err) {
    _didIteratorError = true;
    _iteratorError = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion && _iterator.return) {
        _iterator.return();
      }
    } finally {
      if (_didIteratorError) {
        throw _iteratorError;
      }
    }
  }

  var container = document.querySelector(".script-stage").children[0];
  ReactDOM.render(React.createElement(App, { mazeLayout: mazeLayout }), container);
};
main();