import assert from "node:assert/strict";
import {
  describeCountermodel,
  findCountermodel,
  holdsInModel,
  verifyCountermodel,
} from "../syllogisms/countermodel.mjs";
import {
  buildFitchProof,
  categoricalToFormula,
  formatFitchFormula,
  nestProofLines,
  verifyFitchProof,
} from "../syllogisms/fol-proof.mjs";
import {
  CHALLENGE_TEMPLATES,
  entails,
  formatStandardCategorical,
  formatStatement,
  generateChallenge,
  isSatisfiable,
  naturalVariantCount,
  statementKey,
} from "../syllogisms/logic.mjs";

const s = (form, subject, predicate) => ({ form, subject, predicate });

// Barbara: inclusion is transitive.
assert.equal(entails([s("A", 0, 1), s("A", 1, 2)], s("A", 0, 2), 3), true);

// Universal premises have no existential import.
assert.equal(entails([s("A", 0, 1), s("A", 1, 2)], s("I", 0, 2), 3), false);

// E and I convert, while A does not convert in general.
assert.equal(entails([s("E", 0, 1)], s("E", 1, 0), 2), true);
assert.equal(entails([s("I", 0, 1)], s("I", 1, 0), 2), true);
assert.equal(entails([s("A", 0, 1)], s("A", 1, 0), 2), false);

// Darii and Ferio work because an explicit existential premise supplies a witness.
assert.equal(entails([s("I", 0, 1), s("A", 1, 2)], s("I", 0, 2), 3), true);
assert.equal(entails([s("I", 0, 1), s("E", 1, 2)], s("O", 0, 2), 3), true);

assert.equal(isSatisfiable([s("A", 0, 1), s("O", 0, 1)], 2), false);
assert.equal(isSatisfiable([s("A", 0, 1), s("E", 0, 1)], 2), true);

const terms = ["诗人", "医生"];
const standardForms = {
  A: "所有S都是M",
  E: "没有S是M",
  I: "有些S是M",
  O: "有些S不是M",
};

for (const form of ["A", "E", "I", "O"]) {
  const variants = new Set(
    Array.from({ length: naturalVariantCount(form) }, (_, wordingVariant) =>
      formatStatement({ ...s(form, 0, 1), wordingVariant }, terms),
    ),
  );
  assert.equal(variants.size, naturalVariantCount(form));
  assert.equal(
    formatStatement({ ...s(form, 0, 1), wordingVariant: 4 }, terms, {
      mode: "letters",
    }),
    standardForms[form],
  );
}

assert.equal(
  formatStatement({ ...s("A", 0, 1), wordingVariant: 3 }, terms),
  "只有医生才是诗人",
);
assert.equal(
  formatStatement({ ...s("O", 0, 1), wordingVariant: 3 }, terms),
  "并非所有诗人都是医生",
);
assert.equal(
  formatStandardCategorical({ ...s("A", 0, 1), wordingVariant: 3 }, terms),
  "所有诗人都是医生",
);

const barbaraPremises = [s("A", 0, 1), s("A", 1, 2)];
const barbaraConclusion = s("A", 0, 2);
const barbaraProof = buildFitchProof(
  barbaraPremises,
  barbaraConclusion,
  3,
);
assert.equal(barbaraProof.kind, "first-order");
assert.equal(
  verifyFitchProof(
    barbaraProof,
    barbaraPremises,
    barbaraConclusion,
    3,
  ),
  true,
);
assert.ok(barbaraProof.lines.some(({ rule }) => rule === "assumption"));
assert.equal(barbaraProof.lines[0].ruleLabel, "前提");
assert.equal(
  barbaraProof.lines.find(({ rule }) => rule === "assumption").ruleLabel,
  "假设",
);
assert.equal(barbaraProof.lines.at(-1).rule, "forall-intro");
assert.equal(barbaraProof.lines.length, 9);
assert.equal(
  formatFitchFormula(
    categoricalToFormula(barbaraConclusion),
    ["诗人", "医生", "画家"],
  ),
  "∀x(诗人(x) → 画家(x))",
);
assert.equal(
  formatFitchFormula(
    categoricalToFormula(barbaraConclusion),
    ["诗人", "医生", "画家"],
    { mode: "letters" },
  ),
  "∀x(S(x) → P(x))",
);

const dariiProof = buildFitchProof(
  [s("I", 0, 1), s("A", 1, 2)],
  s("I", 0, 2),
  3,
);
const witnessAssumption = dariiProof.lines.find(
  ({ assumptionKind }) => assumptionKind === "existential",
);
assert.equal(witnessAssumption.ruleLabel, "假设");

const barbaraTree = nestProofLines(barbaraProof.lines);
const flattenTree = (nodes) =>
  nodes.flatMap((node) =>
    node.kind === "line" ? [node.line.number] : flattenTree(node.children),
  );
assert.deepEqual(
  flattenTree(barbaraTree),
  barbaraProof.lines.map(({ number }) => number),
);

const mutatedBarbaraProof = structuredClone(barbaraProof);
mutatedBarbaraProof.lines[4].formula.predicate = 2;
assert.equal(
  verifyFitchProof(
    mutatedBarbaraProof,
    barbaraPremises,
    barbaraConclusion,
    3,
  ),
  false,
);

const forwardReferenceProof = structuredClone(barbaraProof);
forwardReferenceProof.lines[3].refs = [forwardReferenceProof.lines.length];
assert.equal(
  verifyFitchProof(
    forwardReferenceProof,
    barbaraPremises,
    barbaraConclusion,
    3,
  ),
  false,
);

const invalidConversionModel = findCountermodel(
  [s("A", 0, 1)],
  s("A", 1, 0),
  2,
);
assert.equal(
  verifyCountermodel(
    invalidConversionModel,
    [s("A", 0, 1)],
    s("A", 1, 0),
  ),
  true,
);
assert.equal(invalidConversionModel.masks.length, 1);
assert.equal(holdsInModel(s("A", 1, 0), invalidConversionModel.masks), false);

const noExistentialImportModel = findCountermodel(
  [s("A", 0, 1)],
  s("I", 0, 1),
  2,
);
assert.deepEqual(noExistentialImportModel.masks, [0]);

const twoWitnessModel = findCountermodel(
  [s("I", 0, 1), s("O", 0, 1)],
  s("A", 0, 1),
  2,
);
assert.equal(twoWitnessModel.masks.length, 2);

const describedModel = describeCountermodel(
  invalidConversionModel,
  [s("A", 0, 1)],
  s("A", 1, 0),
  terms,
);
assert.equal(describedModel.checks[0].truth, true);
assert.equal(describedModel.checks.at(-1).truth, false);
assert.match(describedModel.checks.at(-1).reason, /但不是/);

let exhaustiveValidCount = 0;
let exhaustiveInvalidCount = 0;

for (const premises of CHALLENGE_TEMPLATES) {
  const termCount =
    Math.max(
      ...premises.flatMap(({ subject, predicate }) => [subject, predicate]),
    ) + 1;

  for (const form of ["A", "E", "I", "O"]) {
    for (let subject = 0; subject < termCount; subject += 1) {
      for (let predicate = 0; predicate < termCount; predicate += 1) {
        if (subject === predicate) continue;
        const conclusion = s(form, subject, predicate);

        if (entails(premises, conclusion, termCount)) {
          exhaustiveValidCount += 1;
          const proof = buildFitchProof(
            premises,
            conclusion,
            termCount,
          );
          assert.equal(
            verifyFitchProof(
              proof,
              premises,
              conclusion,
              termCount,
            ),
            true,
          );
          assert.equal(
            findCountermodel(premises, conclusion, termCount),
            null,
          );
        } else {
          exhaustiveInvalidCount += 1;
          const model = findCountermodel(
            premises,
            conclusion,
            termCount,
          );
          assert.equal(
            verifyCountermodel(model, premises, conclusion),
            true,
          );
        }
      }
    }
  }
}

assert.ok(exhaustiveValidCount > 100);
assert.ok(exhaustiveInvalidCount > 500);

let seed = 0x5eed1234;
const random = () => {
  seed = (1664525 * seed + 1013904223) >>> 0;
  return seed / 2 ** 32;
};
let followsCount = 0;
let doesNotFollowCount = 0;

for (let index = 0; index < 300; index += 1) {
  const challenge = generateChallenge(random);
  const premiseKeys = new Set(challenge.premises.map(statementKey));

  assert.equal(isSatisfiable(challenge.premises, challenge.terms.length), true);
  assert.equal(premiseKeys.has(statementKey(challenge.conclusion)), false);
  assert.equal(
    challenge.follows,
    entails(challenge.premises, challenge.conclusion, challenge.terms.length),
  );

  if (challenge.follows) {
    followsCount += 1;
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
    doesNotFollowCount += 1;
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

assert.ok(followsCount > 100);
assert.ok(doesNotFollowCount > 100);

let previousSignature = "";

for (const requiredFollows of [true, false]) {
  for (let index = 0; index < 100; index += 1) {
    const challenge = generateChallenge(random, previousSignature, requiredFollows);
    previousSignature = challenge.signature;
    assert.equal(challenge.follows, requiredFollows);
  }
}

assert.throws(() => generateChallenge(random, "", "yes"), TypeError);

console.log(
  `Syllogism semantics, Fitch proofs, countermodels, ${exhaustiveValidCount + exhaustiveInvalidCount} exhaustive template conclusions, 300 random challenges, wording modes, and forced-answer construction passed.`,
);
