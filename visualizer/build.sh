cat compiled/react.js > compiled/out.js
npx babel src/visualizer.js --presets react-app/prod >> compiled/out.js