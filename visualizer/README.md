# Building

To constantly watch and recompile visualizer

```bash
cd visualizer
npm i
npx babel --watch src --out-dir out --presets react-app/prod
```

the script is in the `src` directory and will be output in the `out` directory

# Running in Sterling

First open the developer console
([Chrome](https://developer.mozilla.org/en-US/docs/Tools/Browser_Console),
[Firefox](https://developer.mozilla.org/en-US/docs/Tools/Browser_Console#opening_the_browser_console))
and paste in the following:

```js
fetch("https://unpkg.com/react@17.0.2/umd/react.development.js")
  .then((response) => response.text())
  .then((data) => {
    eval(data);
    console.log("Loaded react");
  })
  .then(() => {
    return fetch(
      "https://unpkg.com/react-dom@17.0.2/umd/react-dom.development.js"
    );
  })
  .then((response) => response.text())
  .then((data) => {
    eval(data);
    console.log("Loaded react-dom");
  });
```

This will load the relevant libraries. Then paste in the visualizer (from the
`out` directory) and hit execute.
