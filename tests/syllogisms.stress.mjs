import assert from "node:assert/strict";
import {
  findCountermodel,
  holdsInModel,
  verifyCountermodel,
} from "../syllogisms/countermodel.mjs";
import {
  buildFitchProof,
  verifyFitchProof,
} from "../syllogisms/fol-proof.mjs";
import {
  entails,
  generateChallenge,
  isSatisfiable,
  statementKey,
} from "../syllogisms/logic.mjs";

const FORMS = Object.freeze(["A", "E", "I", "O"]);
const TERM_COUNT = 3;
const TYPE_COUNT = 2 ** TERM_COUNT;
const MODEL_COUNT = 2 ** TYPE_COUNT - 1;
const ALL_MODELS = (1n << BigInt(MODEL_COUNT)) - 1n;

const statement = (form, subject, predicate) => ({
  form,
  subject,
  predicate,
});

const statements = FORMS.flatMap((form) =>
  Array.from({ length: TERM_COUNT }, (_, subject) =>
    Array.from({ length: TERM_COUNT }, (_, predicate) =>
      subject === predicate ? null : statement(form, subject, predicate),
    ),
  ).flat(),
).filter(Boolean);

function populationCount(value) {
  let remaining = value;
  let count = 0;
  while (remaining > 0) {
    count += remaining & 1;
    remaining >>>= 1;
  }
  return count;
}

function independentHolds(item, model) {
  const types = [];
  for (let type = 0; type < TYPE_COUNT; type += 1) {
    if ((model & (1 << type)) !== 0) types.push(type);
  }

  const hasSubject = (type) => (type & (1 << item.subject)) !== 0;
  const hasPredicate = (type) => (type & (1 << item.predicate)) !== 0;

  if (item.form === "A") {
    return types.every((type) => !hasSubject(type) || hasPredicate(type));
  }
  if (item.form === "E") {
    return types.every((type) => !hasSubject(type) || !hasPredicate(type));
  }
  if (item.form === "I") {
    return types.some((type) => hasSubject(type) && hasPredicate(type));
  }
  return types.some((type) => hasSubject(type) && !hasPredicate(type));
}

const modelBitsByStatement = new Map(
  statements.map((item) => {
    let bits = 0n;
    for (let model = 1; model <= MODEL_COUNT; model += 1) {
      if (independentHolds(item, model)) {
        bits |= 1n << BigInt(model - 1);
      }
    }
    return [statementKey(item), bits];
  }),
);

function satisfyingModelBits(premises) {
  return premises.reduce(
    (bits, item) => bits & modelBitsByStatement.get(statementKey(item)),
    ALL_MODELS,
  );
}

function independentEntails(premiseBits, conclusion) {
  const conclusionBits = modelBitsByStatement.get(statementKey(conclusion));
  return (premiseBits & (ALL_MODELS ^ conclusionBits)) === 0n;
}

function minimumDomainSize(modelBits) {
  let minimum = Number.POSITIVE_INFINITY;
  for (let model = 1; model <= MODEL_COUNT; model += 1) {
    if ((modelBits & (1n << BigInt(model - 1))) !== 0n) {
      minimum = Math.min(minimum, populationCount(model));
    }
  }
  return minimum;
}

function modelNumberFromMasks(masks) {
  return masks.reduce((model, type) => model | (1 << type), 0);
}

function* combinations(items, size, start = 0, chosen = []) {
  if (chosen.length === size) {
    yield [...chosen];
    return;
  }
  const remaining = size - chosen.length;
  for (let index = start; index <= items.length - remaining; index += 1) {
    chosen.push(items[index]);
    yield* combinations(items, size, index + 1, chosen);
    chosen.pop();
  }
}

let premiseSetCount = 0;
let satisfiablePremiseSetCount = 0;
let inferenceCount = 0;
let validInferenceCount = 0;
let invalidInferenceCount = 0;
let maximumProofLines = 0;
let maximumCountermodelSize = 0;

for (let premiseCount = 0; premiseCount <= 4; premiseCount += 1) {
  for (const premises of combinations(statements, premiseCount)) {
    premiseSetCount += 1;
    const premiseBits = satisfyingModelBits(premises);
    const independentlySatisfiable = premiseBits !== 0n;
    assert.equal(
      isSatisfiable(premises, TERM_COUNT),
      independentlySatisfiable,
      `satisfiability mismatch for ${premises.map(statementKey).join("|")}`,
    );
    if (!independentlySatisfiable) continue;
    satisfiablePremiseSetCount += 1;

    for (const conclusion of statements) {
      inferenceCount += 1;
      const independentlyValid = independentEntails(premiseBits, conclusion);
      assert.equal(
        entails(premises, conclusion, TERM_COUNT),
        independentlyValid,
        `entailment mismatch for ${premises
          .map(statementKey)
          .join("|")} => ${statementKey(conclusion)}`,
      );

      if (independentlyValid) {
        validInferenceCount += 1;
        const proof = buildFitchProof(premises, conclusion, TERM_COUNT);
        assert.equal(
          verifyFitchProof(proof, premises, conclusion, TERM_COUNT),
          true,
        );
        assert.equal(findCountermodel(premises, conclusion, TERM_COUNT), null);
        maximumProofLines = Math.max(maximumProofLines, proof.lines.length);
      } else {
        invalidInferenceCount += 1;
        const countermodel = findCountermodel(
          premises,
          conclusion,
          TERM_COUNT,
        );
        assert.equal(
          verifyCountermodel(countermodel, premises, conclusion),
          true,
        );
        const concreteModel = modelNumberFromMasks(countermodel.masks);
        assert.notEqual(concreteModel, 0);
        assert.ok(premises.every((item) => independentHolds(item, concreteModel)));
        assert.equal(independentHolds(conclusion, concreteModel), false);
        const counterexampleBits =
          premiseBits &
          (ALL_MODELS ^ modelBitsByStatement.get(statementKey(conclusion)));
        assert.equal(
          countermodel.masks.length,
          minimumDomainSize(counterexampleBits),
        );
        maximumCountermodelSize = Math.max(
          maximumCountermodelSize,
          countermodel.masks.length,
        );
      }
    }
  }
}

let seed = 0x71c0ffee;
const random = () => {
  seed = (1664525 * seed + 1013904223) >>> 0;
  return seed / 2 ** 32;
};

let randomValidCount = 0;
let randomInvalidCount = 0;
let previousSignature = "";

for (let index = 0; index < 5_000; index += 1) {
  const challenge = generateChallenge(random, previousSignature);
  previousSignature = challenge.signature;
  assert.equal(
    challenge.follows,
    entails(challenge.premises, challenge.conclusion, challenge.terms.length),
  );
  assert.equal(
    new Set(challenge.premises.map(statementKey)).has(
      statementKey(challenge.conclusion),
    ),
    false,
  );
  assert.equal(
    isSatisfiable(challenge.premises, challenge.terms.length),
    true,
  );

  if (challenge.follows) {
    randomValidCount += 1;
    const proof = buildFitchProof(
      challenge.premises,
      challenge.conclusion,
      challenge.terms.length,
    );
    assert.equal(
      verifyFitchProof(
        proof,
        challenge.premises,
        challenge.conclusion,
        challenge.terms.length,
      ),
      true,
    );
  } else {
    randomInvalidCount += 1;
    const countermodel = findCountermodel(
      challenge.premises,
      challenge.conclusion,
      challenge.terms.length,
    );
    assert.equal(
      verifyCountermodel(
        countermodel,
        challenge.premises,
        challenge.conclusion,
      ),
      true,
    );
  }
}

assert.ok(randomValidCount > 2_300 && randomValidCount < 2_700);
assert.equal(randomValidCount + randomInvalidCount, 5_000);

for (const requiredFollows of [true, false]) {
  for (let index = 0; index < 2_000; index += 1) {
    const challenge = generateChallenge(
      random,
      previousSignature,
      requiredFollows,
    );
    previousSignature = challenge.signature;
    assert.equal(challenge.follows, requiredFollows);
  }
}

assert.equal(holdsInModel(statement("A", 0, 1), [0]), true);
assert.equal(holdsInModel(statement("I", 0, 1), [0]), false);

console.log(
  [
    `${premiseSetCount} premise sets (${satisfiablePremiseSetCount} satisfiable)`,
    `${inferenceCount} independently checked inferences`,
    `${validInferenceCount} verified Fitch proofs`,
    `${invalidInferenceCount} verified minimum countermodels`,
    `maximum proof ${maximumProofLines} lines`,
    `maximum countermodel ${maximumCountermodelSize} objects`,
    `5000 random and 4000 forced-answer challenges`,
  ].join("; "),
);
