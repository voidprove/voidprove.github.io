import assert from "node:assert/strict";

import {
  analyzeRuleUsage,
  checkChallengeProof,
} from "../fitch/challenge-checker.mjs";

const line = (formula, rule, citations = "", path = [], isAssumption = false) => ({
  formula,
  rule,
  citations,
  path,
  isAssumption,
});

const assumption = (formula, path) =>
  line(formula, "assumption", "", path, true);

const basic = checkChallengeProof({
  premises: ["p → q", "p"],
  target: "q",
  lines: [line("q", "implies-elim", "1, 2")],
});
assert.equal(basic.ok, true);
assert.equal(basic.ruleUsage.usesDerivedRules, false);
assert.deepEqual(basic.ruleUsage.derivedOccurrences, []);

const derived = checkChallengeProof({
  premises: ["p ∨ q", "¬p"],
  target: "q",
  lines: [line("q", "析取三段论", "1, 2")],
});
assert.equal(derived.ok, true);
assert.equal(derived.ruleUsage.usesDerivedRules, true);
assert.deepEqual(derived.ruleUsage.derivedRuleIds, ["disjunctive-syllogism"]);
assert.deepEqual(derived.ruleUsage.derivedOccurrences[0], {
  lineId: null,
  lineIndex: 0,
  lineNumber: 3,
  id: "disjunctive-syllogism",
  label: "析取三段论",
  kind: "derived",
});

const repeatedUsage = analyzeRuleUsage(
  [
    line("p", "双重否定消去", "1"),
    line("p", "double-negation", "1"),
    line("q", "重申", "2"),
  ],
  1,
);
assert.deepEqual(repeatedUsage.derivedRuleIds, ["double-negation"]);
assert.deepEqual(
  repeatedUsage.derivedOccurrences.map(({ lineNumber }) => lineNumber),
  [2, 3],
);

const mismatch = checkChallengeProof({
  premises: ["p"],
  target: "q",
  lines: [line("p", "reiteration", "1")],
});
assert.equal(mismatch.ok, false);
assert.equal(mismatch.error.code, "CONCLUSION_MISMATCH");
assert.equal(mismatch.error.lineNumber, 2);

const openAssumption = checkChallengeProof({
  premises: [],
  target: "p",
  lines: [assumption("p", ["box"])],
});
assert.equal(openAssumption.ok, false);
assert.equal(openAssumption.error.code, "CONCLUSION_NOT_AT_ROOT");
assert.equal(openAssumption.error.lineNumber, 1);

const earlierCoreError = checkChallengeProof({
  premises: ["p"],
  target: "q",
  lines: [line("q", "reiteration", "1")],
});
assert.equal(earlierCoreError.ok, false);
assert.equal(earlierCoreError.error.code, "RULE_NOT_SATISFIED");
assert.equal(earlierCoreError.error.lineNumber, 2);

const noLines = checkChallengeProof({ premises: [], target: "p → p", lines: [] });
assert.equal(noLines.ok, false);
assert.equal(noLines.error.code, "EMPTY_PROOF");

const invalidTarget = checkChallengeProof({
  premises: ["p"],
  target: "P(",
  lines: [line("p", "reiteration", "1")],
});
assert.equal(invalidTarget.ok, false);
assert.equal(invalidTarget.error.code, "INVALID_TARGET");

const surfaceEquivalentTarget = checkChallengeProof({
  premises: [],
  target: "p 蕴含 p",
  lines: [
    assumption("p", ["box"]),
    line("p", "reiteration", "1", ["box"]),
    line("(p → p)", "implies-intro", "1-2"),
  ],
});
assert.equal(surfaceEquivalentTarget.ok, true);

const merelyTruthEquivalent = checkChallengeProof({
  premises: ["q ∨ p"],
  target: "p ∨ q",
  lines: [line("q ∨ p", "reiteration", "1")],
});
assert.equal(merelyTruthEquivalent.ok, false);
assert.equal(merelyTruthEquivalent.error.code, "CONCLUSION_MISMATCH");

const targetOnlyEarlier = checkChallengeProof({
  premises: ["p", "q"],
  target: "p",
  lines: [
    line("p", "reiteration", "1"),
    line("q", "reiteration", "2"),
  ],
});
assert.equal(targetOnlyEarlier.ok, false);
assert.equal(targetOnlyEarlier.error.code, "CONCLUSION_MISMATCH");
assert.equal(targetOnlyEarlier.error.lineNumber, 4);
assert.equal(targetOnlyEarlier.error.proofLineIndex, 1);

const openAndWrong = checkChallengeProof({
  premises: [],
  target: "q",
  lines: [assumption("p", ["box"])],
});
assert.equal(openAndWrong.ok, false);
assert.equal(openAndWrong.error.code, "CONCLUSION_NOT_AT_ROOT");

const firstOrderConfiguration = checkChallengeProof({
  premises: ["∀x P(x)"],
  target: "P(a)",
  lines: [line("P(a)", "forall-elim", "1")],
});
assert.equal(firstOrderConfiguration.ok, false);
assert.equal(firstOrderConfiguration.error.code, "NON_PROPOSITIONAL_TARGET");

const invalidCoreWins = checkChallengeProof({
  premises: ["p"],
  target: "P(",
  lines: [line("q", "reiteration", "1")],
});
assert.equal(invalidCoreWins.ok, false);
assert.equal(invalidCoreWins.error.code, "RULE_NOT_SATISFIED");

console.log("Fitch challenge goal and derived-rule usage tests passed.");
