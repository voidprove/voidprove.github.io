import assert from "node:assert/strict";

import {
  PROPOSITIONAL_ADVANCED_TEMPLATE_IDS,
  PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS,
  createPropositionalChallengeSampler,
} from "../fitch/propositional-challenges.mjs";

function seededRandom(seed) {
  let state = seed >>> 0;
  return () => {
    state = (1664525 * state + 1013904223) >>> 0;
    return state / 2 ** 32;
  };
}

const sampleSize = Number(process.env.FITCH_STRESS_SAMPLES ?? 10_000);
assert.ok(
  Number.isInteger(sampleSize) && sampleSize >= 5_000,
  "FITCH_STRESS_SAMPLES must be an integer of at least 5000",
);
const sampler = createPropositionalChallengeSampler({
  random: seededRandom(0xc0ffee),
});
const counts = { direct: 0, light: 0, substantial: 0 };
const templates = new Set();
const advancedTemplateIds = new Set(PROPOSITIONAL_ADVANCED_TEMPLATE_IDS);
const advancedTemplates = new Set();
const templateCounts = new Map();
const argumentsSeen = new Set();
const attempts = [];
let fallbackCount = 0;
let noveltyRelaxedCount = 0;
let maximumAttempts = 0;
let advancedCount = 0;
let peirceCount = 0;
let atomicPeirceCount = 0;
let depthThreeCount = 0;

for (let index = 0; index < sampleSize; index += 1) {
  const challenge = sampler.sample();
  const { difficulty } = challenge;
  counts[difficulty.band] += 1;
  templates.add(challenge.templateId);
  templateCounts.set(
    challenge.templateId,
    (templateCounts.get(challenge.templateId) ?? 0) + 1,
  );
  argumentsSeen.add(
    `${[...challenge.premises].sort().join(";")}⊢${challenge.conclusion}`,
  );
  if (advancedTemplateIds.has(challenge.templateId)) {
    advancedCount += 1;
    advancedTemplates.add(challenge.templateId);
  }
  if (challenge.templateId === "peirce-law") {
    peirceCount += 1;
    if (/^\(\(([pqr]) → ([pqr])\) → \1\) → \1$/u.test(challenge.conclusion)) {
      atomicPeirceCount += 1;
    }
  }
  if (difficulty.metrics.maxDepth >= 3) depthThreeCount += 1;
  if (difficulty.sampling.fallbackUsed) fallbackCount += 1;
  if (difficulty.sampling.noveltyRelaxed) noveltyRelaxedCount += 1;
  maximumAttempts = Math.max(maximumAttempts, difficulty.sampling.attempts);
  attempts.push(difficulty.sampling.attempts);
  assert.equal(difficulty.band, difficulty.sampling.targetBand);
}

const expected = { direct: 0.3, light: 0.2, substantial: 0.5 };
for (const [band, probability] of Object.entries(expected)) {
  const observed = counts[band] / sampleSize;
  assert.ok(
    Math.abs(observed - probability) < 0.015,
    `${band} distribution drifted to ${(observed * 100).toFixed(2)}%`,
  );
}
assert.deepEqual(
  [...templates].sort(),
  [...PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS].sort(),
);
assert.deepEqual(
  [...advancedTemplates].sort(),
  [...PROPOSITIONAL_ADVANCED_TEMPLATE_IDS].sort(),
);
assert.ok(
  fallbackCount / sampleSize < 0.002,
  `fallback rate rose to ${fallbackCount}/${sampleSize}`,
);
assert.ok(noveltyRelaxedCount <= fallbackCount);
const advancedShare = advancedCount / sampleSize;
assert.ok(
  Math.abs(advancedShare - 0.1) < 0.02,
  `advanced tail drifted to ${(advancedShare * 100).toFixed(2)}%`,
);
const peirceShare = peirceCount / sampleSize;
assert.ok(
  peirceShare > 0.025 && peirceShare < 0.055,
  `Peirce's law drifted to ${(peirceShare * 100).toFixed(2)}%`,
);
assert.ok(
  atomicPeirceCount / sampleSize > 0.012,
  `atomic Peirce visibility fell to ${atomicPeirceCount}/${sampleSize}`,
);
assert.ok(
  depthThreeCount / sampleSize > 0.05,
  `deep-proof share fell to ${depthThreeCount}/${sampleSize}`,
);
assert.ok(
  argumentsSeen.size / sampleSize > 0.6,
  `only ${argumentsSeen.size}/${sampleSize} arguments were distinct`,
);
assert.ok(
  Math.max(...templateCounts.values()) / sampleSize < 0.16,
  "one challenge template dominates the output",
);
attempts.sort((left, right) => left - right);
const meanAttempts =
  attempts.reduce((sum, count) => sum + count, 0) / sampleSize;
const p99Attempts = attempts[Math.ceil(sampleSize * 0.99) - 1];
assert.ok(meanAttempts < 2.5, `mean attempts rose to ${meanAttempts.toFixed(3)}`);
assert.ok(p99Attempts <= 16, `p99 attempts rose to ${p99Attempts}`);

console.log(
  `Fitch difficulty distribution passed ${sampleSize} samples: ` +
    `${counts.direct}/${counts.light}/${counts.substantial} ` +
    `direct/light/substantial; ${advancedCount} advanced; ` +
    `${peirceCount} Peirce (${atomicPeirceCount} atomic); ` +
    `${argumentsSeen.size} distinct; mean/p99/max attempts ` +
    `${meanAttempts.toFixed(3)}/${p99Attempts}/${maximumAttempts}; ` +
    `${fallbackCount} fallbacks.`,
);
