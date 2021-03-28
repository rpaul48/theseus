const e = React.createElement;

function main() {
  const domContainer = div;
  ReactDOM.render(LikeButton, domContainer);
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

    return <button onClick={() => this.setState({ liked: true })}>Like</button>;
  }
}

main();
