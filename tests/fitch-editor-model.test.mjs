import assert from "node:assert/strict";

import {
  citationNumbers,
  citationReferencesLine,
  makeSubproofAssumption,
  moveLineToParentScope,
  pathForNextLine,
  shiftCitationsForAddedPremise,
  shiftCitationsForRemovedPremise,
} from "../fitch/editor-model.mjs";

assert.deepEqual(citationNumbers("1, 3-5, 8–10"), [1, 3, 5, 8, 10]);
assert.equal(citationReferencesLine("1, 3-5", 3), true);
assert.equal(citationReferencesLine("1, 3-5", 4), false);
assert.equal(shiftCitationsForAddedPremise("1, 2, 3-5", 2), "1, 2, 4-6");
assert.equal(shiftCitationsForRemovedPremise("1, 3, 4-7", 2), "1, 2, 3-6");

const rootLine = {
  id: 1,
  formula: "p",
  rule: "reiteration",
  citations: "1",
  path: [],
  isAssumption: false,
};
const assumption = makeSubproofAssumption(rootLine, "scope-1");
assert.deepEqual(assumption.path, ["scope-1"]);
assert.equal(assumption.rule, "assumption");
assert.equal(assumption.citations, "");
assert.equal(assumption.isAssumption, true);
assert.deepEqual(pathForNextLine([assumption]), ["scope-1"]);

const nestedLine = {
  ...rootLine,
  path: ["outer", "inner"],
};
assert.deepEqual(moveLineToParentScope(nestedLine).path, ["outer"]);
assert.deepEqual(moveLineToParentScope(assumption), {
  ...assumption,
  path: [],
  isAssumption: false,
  rule: "reiteration",
});

// Model helpers return new records and never alter previously obtained lines.
assert.deepEqual(rootLine.path, []);
assert.equal(rootLine.rule, "reiteration");

console.log("Fitch editor model tests passed.");
