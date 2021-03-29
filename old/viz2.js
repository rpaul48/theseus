function esm(templateStrings, ...substitutions) {
  let js = templateStrings.raw[0];
  for (let i = 0; i < substitutions.length; i++) {
    js += substitutions[i] + templateStrings.raw[i + 1];
  }
  return "data:text/javascript;base64," + btoa(js);
}

m2 = esm`import * as r from 'https://cdn.jsdelivr.net/npm/react@16.12.0/umd/react.development.js'; export default r`;
import(m2);

console.log(react.createElement);
