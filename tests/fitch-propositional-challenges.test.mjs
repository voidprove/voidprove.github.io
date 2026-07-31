import assert from "node:assert/strict";

import { createChallengePolicy } from "../fitch/challenge-difficulty.mjs";
import { parseFormula } from "../fitch/parser.mjs";
import {
  PROPOSITIONAL_ADVANCED_TEMPLATE_IDS,
  PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS,
  PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS,
  createPropositionalChallengeSampler,
  detectOneLineProof,
  evaluatePropositionalFormula,
  isSatisfiablePropositionalSet,
  isValidPropositionalArgument,
  samplePropositionalChallenge,
} from "../fitch/propositional-challenges.mjs";

function seededRandom(seed) {
  let state = seed >>> 0;
  return () => {
    state = (1664525 * state + 1013904223) >>> 0;
    return state / 2 ** 32;
  };
}

const ATOM_PERMUTATIONS = [
  ["p", "q", "r"],
  ["p", "r", "q"],
  ["q", "p", "r"],
  ["q", "r", "p"],
  ["r", "p", "q"],
  ["r", "q", "p"],
];

function challengeShape(challenge) {
  return ATOM_PERMUTATIONS.map((permutation) => {
    const names = Object.fromEntries(
      ["p", "q", "r"].map((name, index) => [name, permutation[index]]),
    );
    const rename = (formula) =>
      formula.replace(/[pqr]/gu, (name) => names[name]);
    return `${challenge.premises.map(rename).sort().join(";")}⊢${rename(
      challenge.conclusion,
    )}`;
  }).sort()[0];
}

function assertPropositional(formula) {
  switch (formula.kind) {
    case "proposition":
      assert.match(formula.name, /^[pqr]$/u);
      return;
    case "not":
      assertPropositional(formula.value);
      return;
    case "binary":
      assert.ok(
        ["and", "or", "implies"].includes(formula.operator),
        `unexpected binary operator: ${formula.operator}`,
      );
      assertPropositional(formula.left);
      assertPropositional(formula.right);
      return;
    default:
      assert.fail(`non-propositional node in challenge: ${formula.kind}`);
  }
}

function formulaDepth(formula) {
  if (formula.kind === "proposition") return 0;
  if (formula.kind === "not") return 1 + formulaDepth(formula.value);
  if (formula.kind === "binary") {
    return 1 + Math.max(formulaDepth(formula.left), formulaDepth(formula.right));
  }
  assert.fail(`non-propositional node in depth measurement: ${formula.kind}`);
}

function collectPropositions(formula, names = new Set()) {
  switch (formula.kind) {
    case "proposition":
      names.add(formula.name);
      return names;
    case "not":
      return collectPropositions(formula.value, names);
    case "binary":
      collectPropositions(formula.left, names);
      collectPropositions(formula.right, names);
      return names;
    default:
      assert.fail(`non-propositional node in independent oracle: ${formula.kind}`);
  }
}

function evaluateIndependently(formula, valuation) {
  if (formula.kind === "proposition") return valuation.get(formula.name);
  if (formula.kind === "not") {
    return !evaluateIndependently(formula.value, valuation);
  }
  if (formula.kind !== "binary") {
    assert.fail(`non-propositional node in independent oracle: ${formula.kind}`);
  }
  const left = evaluateIndependently(formula.left, valuation);
  const right = evaluateIndependently(formula.right, valuation);
  if (formula.operator === "and") return left && right;
  if (formula.operator === "or") return left || right;
  if (formula.operator === "implies") return !left || right;
  if (formula.operator === "iff") return left === right;
  assert.fail(`unknown operator in independent oracle: ${formula.operator}`);
}

function independentValuations(formulas) {
  const names = [...formulas.reduce(
    (result, formula) => collectPropositions(formula, result),
    new Set(),
  )].sort();
  return Array.from({ length: 2 ** names.length }, (_unused, mask) =>
    new Map(names.map((name, bit) => [name, (mask & (1 << bit)) !== 0])),
  );
}

function independentlySatisfiable(formulas) {
  return independentValuations(formulas).some((valuation) =>
    formulas.every((formula) => evaluateIndependently(formula, valuation)),
  );
}

function independentlyValid(premises, conclusion) {
  return independentValuations([...premises, conclusion]).every(
    (valuation) =>
      !premises.every((premise) => evaluateIndependently(premise, valuation)) ||
      evaluateIndependently(conclusion, valuation),
  );
}

const p = parseFormula("p");
const notP = parseFormula("¬p");
assert.equal(evaluatePropositionalFormula(p, { p: true }), true);
assert.equal(evaluatePropositionalFormula(notP, { p: true }), false);
assert.equal(isSatisfiablePropositionalSet([p, notP]), false);
assert.equal(
  isValidPropositionalArgument(
    [parseFormula("p → q"), p],
    parseFormula("q"),
  ),
  true,
);
assert.equal(
  isValidPropositionalArgument([parseFormula("p ∨ q")], p),
  false,
);
assert.equal(
  independentlyValid([p, notP], parseFormula("q")),
  true,
  "an inconsistent premise set entails vacuously",
);
assert.equal(
  independentlySatisfiable([p, notP]),
  false,
  "the independent oracle must separately reject inconsistent premises",
);

const firstRun = createPropositionalChallengeSampler({
  random: seededRandom(20260731),
});
const secondRun = createPropositionalChallengeSampler({
  random: seededRandom(20260731),
});
for (let index = 0; index < 30; index += 1) {
  const first = firstRun.sample();
  const second = secondRun.sample();
  assert.deepEqual(
    first,
    second,
    "seeded challenge sampling must be reproducible",
  );
}

const random = seededRandom(0x5f3759df);
const sampler = createPropositionalChallengeSampler({ random });
const observedTemplates = new Set();
const observedArguments = new Set();
const bandCounts = { direct: 0, light: 0, substantial: 0 };
const templateCounts = new Map();
const advancedTemplateIds = new Set(PROPOSITIONAL_ADVANCED_TEMPLATE_IDS);
const recentShapes = [];
let noPremiseCount = 0;
let premiseCount = 0;
let advancedCount = 0;
let peirceCount = 0;
let atomicPeirceCount = 0;
let depthThreeCount = 0;
let fallbackCount = 0;
let noveltyRelaxedCount = 0;
let adjacentTemplateRepeatCount = 0;
let recentShapeRepeatCount = 0;
let maximumAttempts = 0;
let previousTemplateId = null;
const observedPremiseCounts = new Set();

for (let index = 0; index < 4000; index += 1) {
  const challenge = sampler.sample();
  observedTemplates.add(challenge.templateId);
  templateCounts.set(
    challenge.templateId,
    (templateCounts.get(challenge.templateId) ?? 0) + 1,
  );
  bandCounts[challenge.difficulty.band] += 1;
  observedPremiseCounts.add(challenge.premises.length);
  observedArguments.add(
    `${[...challenge.premises].sort().join(";")}⊢${challenge.conclusion}`,
  );
  if (challenge.premises.length === 0) noPremiseCount += 1;
  else premiseCount += 1;
  if (advancedTemplateIds.has(challenge.templateId)) advancedCount += 1;
  if (challenge.templateId === "peirce-law") {
    peirceCount += 1;
    if (/^\(\(([pqr]) → ([pqr])\) → \1\) → \1$/u.test(challenge.conclusion)) {
      atomicPeirceCount += 1;
    }
    assert.equal(challenge.difficulty.basicOnlyMetrics.maxDepth, 4);
    assert.equal(challenge.difficulty.basicOnlyMetrics.lineCount, 11);
  }
  if (challenge.difficulty.metrics.maxDepth >= 3) depthThreeCount += 1;
  if (challenge.difficulty.sampling.fallbackUsed) fallbackCount += 1;
  if (challenge.difficulty.sampling.noveltyRelaxed) noveltyRelaxedCount += 1;
  if (challenge.templateId === previousTemplateId) {
    adjacentTemplateRepeatCount += 1;
  }
  previousTemplateId = challenge.templateId;
  const shape = challengeShape(challenge);
  if (recentShapes.includes(shape)) recentShapeRepeatCount += 1;
  recentShapes.push(shape);
  if (recentShapes.length > 8) recentShapes.shift();
  maximumAttempts = Math.max(
    maximumAttempts,
    challenge.difficulty.sampling.attempts,
  );

  const premises = challenge.premises.map(parseFormula);
  const conclusion = parseFormula(challenge.conclusion);
  if (challenge.templateId === "peirce-law") {
    const hypothesis = conclusion.left;
    const conditional = hypothesis.left;
    const aFormula = conclusion.right;
    const bFormula = conditional.right;
    assert.deepEqual(hypothesis.right, aFormula);
    assert.deepEqual(conditional.left, aFormula);
    const combinations = new Set(
      independentValuations([aFormula, bFormula]).map(
        (valuation) =>
          `${Number(evaluateIndependently(aFormula, valuation))}${Number(
            evaluateIndependently(bFormula, valuation),
          )}`,
      ),
    );
    assert.equal(
      combinations.size,
      4,
      "Peirce metavariables must be logically independent",
    );
  }
  premises.forEach(assertPropositional);
  assertPropositional(conclusion);
  const propositionNames = [...[...premises, conclusion].reduce(
    (names, formula) => collectPropositions(formula, names),
    new Set(),
  )];
  assert.ok(
    propositionNames.every((name) => ["p", "q", "r"].includes(name)),
    `challenge contains an unexpected proposition: ${propositionNames.join(", ")}`,
  );
  assert.equal(independentlySatisfiable(premises), true);
  assert.equal(independentlyValid(premises, conclusion), true);
  if (premises.length === 0) {
    assert.ok(
      independentValuations([conclusion]).every((valuation) =>
        evaluateIndependently(conclusion, valuation),
      ),
      "a zero-premise challenge conclusion must be a tautology",
    );
  }
  assert.equal(
    new Set(challenge.premises).size,
    challenge.premises.length,
    "challenge premises must not be duplicated",
  );
  if (premises.length > 0) {
    assert.equal(
      independentlyValid([], conclusion),
      false,
      "a premise-driven challenge must not have a tautological conclusion",
    );
    premises.forEach((_premise, premiseIndex) => {
      assert.equal(
        independentlyValid(
          premises.filter((_item, index) => index !== premiseIndex),
          conclusion,
        ),
        false,
        "every displayed premise must be essential",
      );
    });
  }
  assert.equal(challenge.premises.includes(challenge.conclusion), false);
  assert.doesNotMatch(
    `${challenge.premises.join(" ")} ${challenge.conclusion}`,
    /↔|当且仅当|⊥|矛盾/u,
  );
  assert.equal(challenge.difficulty.band, challenge.difficulty.sampling.targetBand);
  assert.equal(
    typeof challenge.difficulty.sampling.noveltyRelaxed,
    "boolean",
  );
  assert.ok(challenge.difficulty.planningCost >= 0);
  assert.ok(
    challenge.difficulty.trivialityScore >= 0 &&
      challenge.difficulty.trivialityScore <= 100,
  );
  assert.ok(
    challenge.difficulty.basicOnlyPlanningCost >=
      challenge.difficulty.planningCost,
  );
  assert.equal(
    challenge.difficulty.derivedShortcutGap,
    challenge.difficulty.basicOnlyPlanningCost -
      challenge.difficulty.planningCost,
  );
  assert.equal(Object.isFrozen(challenge.difficulty), true);
  assert.equal(Object.isFrozen(challenge.difficulty.metrics), true);
  assert.equal(Object.isFrozen(challenge.difficulty.basicOnlyMetrics), true);
  assert.deepEqual(challenge.difficulty.basicOnlyMetrics.derivedRuleIds, []);
}

assert.deepEqual(
  [...observedTemplates].sort(),
  [...PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS].sort(),
  "sampling must reach every validity-preserving template",
);
assert.ok(noPremiseCount > 0, "sampling must include theorem challenges");
assert.ok(premiseCount > 0, "sampling must include challenges with premises");
assert.deepEqual(
  [...observedPremiseCounts].sort(),
  [0, 1, 2, 3],
  "sampling must cover every supported premise count",
);
assert.ok(
  observedArguments.size > 2600,
  `sampling produced only ${observedArguments.size} distinct arguments`,
);
assert.deepEqual(
  Object.keys(PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS).sort(),
  [...PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS].sort(),
);
assert.deepEqual(
  Object.values(PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS).reduce(
    (counts, band) => ({ ...counts, [band]: counts[band] + 1 }),
    { direct: 0, light: 0, substantial: 0 },
  ),
  { direct: 8, light: 5, substantial: 13 },
);
assert.ok(
  bandCounts.direct >= 1000 && bandCounts.direct <= 1400,
  `direct output outside broad 30% range: ${bandCounts.direct}`,
);
assert.ok(
  bandCounts.light >= 600 && bandCounts.light <= 1000,
  `light output outside broad 20% range: ${bandCounts.light}`,
);
assert.ok(
  bandCounts.substantial >= 1800 && bandCounts.substantial <= 2200,
  `substantial output outside broad 50% range: ${bandCounts.substantial}`,
);
assert.ok(
  advancedCount >= 300 && advancedCount <= 500,
  `advanced tail outside broad 10% range: ${advancedCount}`,
);
assert.ok(
  peirceCount >= 100 && peirceCount <= 220,
  `Peirce's law visibility outside broad 3-5% range: ${peirceCount}`,
);
assert.ok(
  atomicPeirceCount >= 50,
  `recognizable atomic Peirce instances were too rare: ${atomicPeirceCount}`,
);
assert.ok(
  depthThreeCount >= 180,
  `too few questions require three nested scopes in the shortest stored proof: ${depthThreeCount}`,
);
assert.ok(fallbackCount < 10, `too many fallback samples: ${fallbackCount}`);
assert.ok(noveltyRelaxedCount <= fallbackCount);
assert.ok(
  adjacentTemplateRepeatCount < 80,
  `too many adjacent template repeats: ${adjacentTemplateRepeatCount}`,
);
assert.ok(
  recentShapeRepeatCount < 20,
  `too many recent alpha-shape repeats: ${recentShapeRepeatCount}`,
);
assert.ok(maximumAttempts <= 64);
const largestTemplateShare =
  Math.max(...templateCounts.values()) / 4000;
assert.ok(
  largestTemplateShare < 0.16,
  `one template dominates ${(largestTemplateShare * 100).toFixed(2)}% of output`,
);
const inverseSimpson =
  1 /
  [...templateCounts.values()].reduce(
    (sum, count) => sum + (count / 4000) ** 2,
    0,
  );
assert.ok(
  inverseSimpson > 12,
  `effective template count is too low: ${inverseSimpson.toFixed(2)}`,
);

for (const [advancedChance, expectAdvanced] of [
  [0, false],
  [1, true],
]) {
  const tailPolicy = createChallengePolicy({
    version: `forced-tail-${advancedChance}`,
    bandWeights: { direct: 0, light: 0, substantial: 1 },
    generation: {
      advancedChanceByBand: { substantial: advancedChance },
      recentChallengeWindow: 0,
      recentShapeWindow: 0,
      recentTemplateWindow: 0,
    },
  });
  const tailSampler = createPropositionalChallengeSampler({
    random: seededRandom(0xabc000 + advancedChance),
    policy: tailPolicy,
  });
  for (let index = 0; index < 120; index += 1) {
    assert.equal(
      advancedTemplateIds.has(tailSampler.sample().templateId),
      expectAdvanced,
    );
  }
}
assert.throws(
  () =>
    createPropositionalChallengeSampler({
      policy: createChallengePolicy({
        version: "impossible-direct-tail",
        bandWeights: { direct: 1, light: 0, substantial: 0 },
        generation: { advancedChanceByBand: { direct: 1 } },
      }),
    }),
  RangeError,
);

let forcedFallbackCalls = 0;
const forcedFallbackSampler = createPropositionalChallengeSampler({
  random: () => (forcedFallbackCalls++ < 3 ? 0 : 0.9),
  policy: createChallengePolicy({
    version: "forced-independent-fallback",
    bandWeights: { direct: 0, light: 0, substantial: 1 },
    generation: {
      advancedChanceByBand: { substantial: 1 },
      recognizableTheoremChance: 0,
      maxMetavariableAttempts: 1,
      metavariableMaxDepth: { substantial: 2 },
      recentChallengeWindow: 0,
      recentShapeWindow: 0,
      recentTemplateWindow: 0,
    },
  }),
});
const forcedFallbackChallenge = forcedFallbackSampler.sample();
assert.equal(forcedFallbackChallenge.templateId, "peirce-law");
const forcedFallbackConclusion = parseFormula(forcedFallbackChallenge.conclusion);
const forcedFallbackA = forcedFallbackConclusion.right;
const forcedFallbackB = forcedFallbackConclusion.left.left.right;
assert.equal(forcedFallbackA.kind, "binary");
assert.equal(forcedFallbackA.operator, "and");
assert.equal(forcedFallbackA.left.operator, "implies");
assert.equal(forcedFallbackA.right.operator, "implies");
assert.ok(formulaDepth(forcedFallbackA) <= 2);
assert.ok(formulaDepth(forcedFallbackB) <= 2);
assert.equal(
  new Set(
    independentValuations([forcedFallbackA, forcedFallbackB]).map(
      (valuation) =>
        `${Number(evaluateIndependently(forcedFallbackA, valuation))}${Number(
          evaluateIndependently(forcedFallbackB, valuation),
        )}`,
    ),
  ).size,
  4,
);

for (const forcedBand of ["direct", "light", "substantial"]) {
  const bandWeights = { direct: 0, light: 0, substantial: 0 };
  bandWeights[forcedBand] = 1;
  const policy = createChallengePolicy({
    version: `forced-${forcedBand}`,
    bandWeights,
  });
  const sampler = createPropositionalChallengeSampler({
    random: seededRandom(forcedBand.length * 7919),
    policy,
  });
  for (let index = 0; index < 200; index += 1) {
    const challenge = sampler.sample();
    assert.equal(challenge.difficulty.band, forcedBand);
    assert.equal(challenge.difficulty.sampling.targetBand, forcedBand);
  }
  for (const constantRandom of [() => 0, () => 1 - Number.EPSILON]) {
    const constantSampler = createPropositionalChallengeSampler({
      random: constantRandom,
      policy,
    });
    assert.equal(constantSampler.sample().difficulty.band, forcedBand);
  }
}

const exhaustedNoveltySampler = createPropositionalChallengeSampler({
  random: () => 0,
  policy: createChallengePolicy({
    version: "constant-novelty-audit",
    bandWeights: { direct: 1, light: 0, substantial: 0 },
  }),
});
let exhaustedNoveltyChallenge = null;
for (let index = 0; index < 12; index += 1) {
  const challenge = exhaustedNoveltySampler.sample();
  if (challenge.difficulty.sampling.noveltyRelaxed) {
    exhaustedNoveltyChallenge = challenge;
    break;
  }
}
assert.ok(
  exhaustedNoveltyChallenge,
  "constant randomness should eventually exhaust the novelty window",
);
assert.equal(exhaustedNoveltyChallenge.difficulty.sampling.attempts, 64);
assert.equal(exhaustedNoveltyChallenge.difficulty.sampling.fallbackUsed, true);

assert.equal(
  detectOneLineProof({ premises: ["p ∧ q"], conclusion: "q" })?.rule,
  "and-elim",
);
assert.equal(
  detectOneLineProof({ premises: ["p → q", "p"], conclusion: "q" })?.rule,
  "implies-elim",
);
assert.equal(
  detectOneLineProof({ premises: ["¬¬p"], conclusion: "p" })?.rule,
  "double-negation",
);
assert.equal(
  detectOneLineProof({ premises: ["p ∨ q"], conclusion: "q ∨ p" }),
  null,
  "truth-equivalence alone must not count as a one-line Fitch proof",
);
const oneCitationPolicy = createChallengePolicy({
  version: "shared-cache-version",
  generation: { maxOneLineCitations: 1 },
});
const twoCitationPolicy = createChallengePolicy({
  version: "shared-cache-version",
  generation: { maxOneLineCitations: 2 },
});
assert.equal(
  detectOneLineProof(
    { premises: ["q", "p"], conclusion: "p ∧ q" },
    oneCitationPolicy,
  ),
  null,
);
assert.equal(
  detectOneLineProof(
    { premises: ["q", "p"], conclusion: "p ∧ q" },
    twoCitationPolicy,
  )?.rule,
  "and-intro",
);
assert.doesNotThrow(() => samplePropositionalChallenge(() => 0));
assert.doesNotThrow(() => samplePropositionalChallenge(() => 1 - Number.EPSILON));
assert.throws(() => samplePropositionalChallenge(() => 1), RangeError);
assert.throws(() => samplePropositionalChallenge(() => -0.01), RangeError);
assert.throws(() => samplePropositionalChallenge(() => Number.NaN), RangeError);

console.log(
  `Propositional challenge generator passed 4000 valid samples across ${observedTemplates.size} templates (${bandCounts.direct}/${bandCounts.light}/${bandCounts.substantial} direct/light/substantial; ${noPremiseCount} with no premises).`,
  `${advancedCount} advanced, ${peirceCount} Peirce (${atomicPeirceCount} atomic), ${observedArguments.size} distinct arguments.`,
);
