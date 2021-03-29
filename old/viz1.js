// react@17.0.2/cjs/react.development.js
// =======================================================
//          ADD REACT AS DEPENDENCY
// =======================================================

let script1 = document.createElement("script");
let script2 = document.createElement("script");
let script1Loaded = false;
let script2Loaded = false;

function main() {
  loadScript1();
}

function loadScript1() {
  document.body.appendChild(script1);

  script1.onload = function () {
    script1Loaded = true;
  };
  script1.onerror = function (e) {
    console.error(e);
    console.error("hi");
  };
  script1.src = "https://unpkg.com/react@17/umd/react.development.js";

  let interval = setInterval(() => {
    if (script1Loaded) {
      console.log("Script 1 loaded");
      window.clearInterval(interval);
      tryLoadScript2();
    } else {
      console.log("Script 1 not loaded");
    }
  }, 100);
}

function tryLoadScript2() {
  document.body.appendChild(script2);

  script2.onload = function () {
    script2Loaded = true;
  };
  script2.onerror = function (e) {
    console.error(e);
    console.error("hi");
  };
  script2.src = "https://unpkg.com/react-dom@17/umd/react-dom.development.js";

  let interval = setInterval(() => {
    if (script2Loaded) {
      console.log("Script 2 loaded");
      window.clearInterval(interval);
      draw_viz();
    } else {
      console.log("Script 2 not loaded");
    }
  }, 100);
}

function draw_viz() {
  const domContainer = div;
  const e = React.createElement;
  ReactDOM.render(e(LikeButton), domContainer);
}

class LikeButton extends React.Component {
  constructor(props) {
    super(props);
    this.state = { liked: false };
  }

  render() {
    if (this.state.liked) {
      return "You liked this.";
    }

    return e(
      "button",
      { onClick: () => this.setState({ liked: true }) },
      "Like"
    );
  }
}

main();
