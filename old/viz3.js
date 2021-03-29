function esm(templateStrings, ...substitutions) {
  let js = templateStrings.raw[0];
  for (let i = 0; i < substitutions.length; i++) {
    js += substitutions[i] + templateStrings.raw[i + 1];
  }
  return "data:text/javascript;base64," + btoa(js);
}

m1 = esm`import * as r1 from 'https://cdn.jsdelivr.net/npm/react@16.12.0/umd/react.development.js'; export default r1`;
import(m1);
m2 = esm`import * as r2 from 'https://cdn.jsdelivr.net/npm/react-dom@16.12.0/cjs/react-dom.development.js'; export default r2`;
import(m2);

console.log(react.createElement);
// console.log(window["react-dom"].render);
