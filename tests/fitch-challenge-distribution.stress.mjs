import assert from "node:assert/strict";

import {
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

const sampleSize = 50_000;
const sampler = createPropositionalChallengeSampler({
  random: seededRandom(0xc0ffee),
});
const counts = { direct: 0, light: 0, substantial: 0 };
const templates = new Set();
let fallbackCount = 0;
let maximumAttempts = 0;

for (let index = 0; index < sampleSize; index += 1) {
  const challenge = sampler.sample();
  const { difficulty } = challenge;
  counts[difficulty.band] += 1;
  templates.add(challenge.templateId);
  if (difficulty.sampling.fallbackUsed) fallbackCount += 1;
  maximumAttempts = Math.max(maximumAttempts, difficulty.sampling.attempts);
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
assert.equal(fallbackCount, 0);

console.log(
  `Fitch difficulty distribution passed ${sampleSize} samples: ` +
    `${counts.direct}/${counts.light}/${counts.substantial} ` +
    `direct/light/substantial; max ${maximumAttempts} attempts.`,
);
