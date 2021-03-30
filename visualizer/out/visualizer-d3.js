/**
 * Function to convert forge integer tuples to javascript integers
 * @param {AlloyTuple} forgeInt
 * @returns integer
 */
var forgeIntToJsInt = function forgeIntToJsInt(forgeInt) {
  return forgeInt.atoms()[0].id();
};

var draw = function draw(mazeLayout) {};

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

  draw(mazeLayout);
};
main();