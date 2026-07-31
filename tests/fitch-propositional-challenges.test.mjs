import assert from "node:assert/strict";

import { createChallengePolicy } from "../fitch/challenge-difficulty.mjs";
import { parseFormula } from "../fitch/parser.mjs";
import {
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

const firstRun = seededRandom(20260731);
const secondRun = seededRandom(20260731);
for (let index = 0; index < 30; index += 1) {
  const first = samplePropositionalChallenge(firstRun);
  const second = samplePropositionalChallenge(secondRun);
  assert.deepEqual(
    first,
    second,
    "seeded challenge sampling must be reproducible",
  );
}

const random = seededRandom(0x5f3759df);
const observedTemplates = new Set();
const observedArguments = new Set();
const bandCounts = { direct: 0, light: 0, substantial: 0 };
let noPremiseCount = 0;
let premiseCount = 0;
const observedPremiseCounts = new Set();

for (let index = 0; index < 4000; index += 1) {
  const challenge = samplePropositionalChallenge(random);
  observedTemplates.add(challenge.templateId);
  bandCounts[challenge.difficulty.band] += 1;
  observedPremiseCounts.add(challenge.premises.length);
  observedArguments.add(`${challenge.premises.join(";")}⊢${challenge.conclusion}`);
  if (challenge.premises.length === 0) noPremiseCount += 1;
  else premiseCount += 1;

  const premises = challenge.premises.map(parseFormula);
  const conclusion = parseFormula(challenge.conclusion);
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
assert.ok(observedArguments.size > 250, "sampling must produce varied arguments");
assert.deepEqual(
  Object.keys(PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS).sort(),
  [...PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS].sort(),
);
assert.deepEqual(
  Object.values(PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS).reduce(
    (counts, band) => ({ ...counts, [band]: counts[band] + 1 }),
    { direct: 0, light: 0, substantial: 0 },
  ),
  { direct: 8, light: 5, substantial: 3 },
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
);
