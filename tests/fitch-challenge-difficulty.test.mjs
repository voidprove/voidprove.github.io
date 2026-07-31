import assert from "node:assert/strict";

import {
  DEFAULT_CHALLENGE_POLICY,
  classifyDifficulty,
  createChallengePolicy,
  measureProofPlan,
  scorePlanMetrics,
  selectDifficultyBand,
  trivialityScore,
} from "../fitch/challenge-difficulty.mjs";

const metrics = (overrides = {}) => ({
  lineCount: 2,
  subproofs: 0,
  multiSubproofRules: 0,
  maxDepth: 0,
  extraDepth: 0,
  distinctRuleIds: ["reiteration"],
  extraDistinctRules: 0,
  derivedRuleIds: [],
  ...overrides,
});

assert.deepEqual(DEFAULT_CHALLENGE_POLICY.bandWeights, {
  direct: 0.3,
  light: 0.2,
  substantial: 0.5,
});
assert.equal(Object.isFrozen(DEFAULT_CHALLENGE_POLICY), true);
assert.equal(Object.isFrozen(DEFAULT_CHALLENGE_POLICY.score.weights), true);

const direct = classifyDifficulty(metrics({ lineCount: 1 }));
assert.deepEqual(direct, {
  band: "direct",
  planningCost: 0,
  trivialityScore: 100,
});

const identity = classifyDifficulty(
  metrics({
    lineCount: 2,
    subproofs: 1,
    maxDepth: 1,
    distinctRuleIds: ["assumption", "implies-intro"],
    extraDistinctRules: 1,
  }),
);
assert.equal(identity.band, "light");
assert.equal(identity.planningCost, 1.5);
assert.equal(identity.trivialityScore, 77);

assert.equal(classifyDifficulty(metrics({ lineCount: 6 })).planningCost, 5);
assert.equal(classifyDifficulty(metrics({ lineCount: 6 })).band, "light");
assert.equal(classifyDifficulty(metrics({ lineCount: 7 })).band, "substantial");
assert.equal(trivialityScore(5), 50);

const percentagePolicy = createChallengePolicy({
  bandWeights: { direct: 30, light: 20, substantial: 50 },
});
const fractionalPolicy = createChallengePolicy({
  bandWeights: { direct: 0.3, light: 0.2, substantial: 0.5 },
});
assert.deepEqual(percentagePolicy.bandWeights, fractionalPolicy.bandWeights);
assert.deepEqual(
  createChallengePolicy({
    bandWeights: {
      direct: Number.MAX_VALUE,
      light: Number.MAX_VALUE,
      substantial: Number.MAX_VALUE,
    },
  }).bandWeights,
  { direct: 1 / 3, light: 1 / 3, substantial: 1 / 3 },
);
assert.equal(selectDifficultyBand(0, percentagePolicy), "direct");
assert.equal(selectDifficultyBand(0.299999, percentagePolicy), "direct");
assert.equal(selectDifficultyBand(0.3, percentagePolicy), "light");
assert.equal(selectDifficultyBand(0.499999, percentagePolicy), "light");
assert.equal(selectDifficultyBand(0.5, percentagePolicy), "substantial");
assert.equal(
  selectDifficultyBand(
    1 - Number.EPSILON / 2,
    createChallengePolicy({
      bandWeights: { direct: 1, light: 9, substantial: 0 },
    }),
  ),
  "light",
);

const changedWeights = createChallengePolicy({
  score: {
    weights: {
      linesAfterFirst: 2,
      subproofs: 3,
      multiSubproofRules: 4,
      extraDepth: 5,
      extraDistinctRules: 6,
    },
  },
});
const weightedMetrics = metrics({
  lineCount: 3,
  subproofs: 1,
  multiSubproofRules: 1,
  extraDepth: 1,
  extraDistinctRules: 1,
});
assert.equal(scorePlanMetrics(weightedMetrics, changedWeights), 22);

const extremePolicy = createChallengePolicy({
  score: {
    normalizationScale: Number.MAX_VALUE,
    weights: { linesAfterFirst: Number.MAX_VALUE },
  },
});
const extremeCost = scorePlanMetrics(metrics({ lineCount: 3 }), extremePolicy);
assert.equal(extremeCost, Number.MAX_VALUE);
assert.equal(trivialityScore(extremeCost, extremePolicy), 50);

const measured = measureProofPlan([
  {
    formula: "p ∨ q",
    rule: "assumption",
    citations: "",
    path: ["outer"],
    isAssumption: true,
  },
  {
    formula: "p",
    rule: "假设",
    citations: "",
    path: ["outer", "left"],
    isAssumption: true,
  },
  {
    formula: "q",
    rule: "析取消去",
    citations: "1, 2-2, 2-2",
    path: [],
    isAssumption: false,
  },
]);
assert.equal(measured.lineCount, 3);
assert.equal(measured.subproofs, 2);
assert.equal(measured.multiSubproofRules, 1);
assert.equal(measured.maxDepth, 2);
assert.equal(measured.extraDepth, 1);

assert.throws(
  () => createChallengePolicy({ bandWeights: { direct: 0, light: 0, substantial: 0 } }),
  RangeError,
);
assert.throws(
  () => createChallengePolicy({ score: { weights: { subproofs: -1 } } }),
  RangeError,
);
assert.throws(
  () => createChallengePolicy({ score: { multiSubproofRuleIds: ["unknown"] } }),
  TypeError,
);
assert.throws(
  () => createChallengePolicy({ score: { multiSubproofRuleIds: ["assumption"] } }),
  TypeError,
);
assert.throws(
  () => createChallengePolicy({ generation: { maxOneLineCitations: 3 } }),
  RangeError,
);
assert.throws(() => selectDifficultyBand(1), RangeError);

console.log("Fitch challenge difficulty policy and score tests passed.");
