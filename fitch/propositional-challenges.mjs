import {
  DEFAULT_CHALLENGE_POLICY,
  DIFFICULTY_BANDS,
  classifyDifficulty,
  createChallengePolicy,
  measureProofPlan,
  selectDifficultyBand,
} from "./challenge-difficulty.mjs?v=random7";
import { checkChallengeProof } from "./challenge-checker.mjs?v=random7";
import { RULE_OPTIONS } from "./checker.mjs?v=random7";
import { formatFormula } from "./parser.mjs?v=random7";

const ATOM_NAMES = Object.freeze(["p", "q", "r"]);
const ATOM_PERMUTATIONS = Object.freeze([
  Object.freeze(["p", "q", "r"]),
  Object.freeze(["p", "r", "q"]),
  Object.freeze(["q", "p", "r"]),
  Object.freeze(["q", "r", "p"]),
  Object.freeze(["r", "p", "q"]),
  Object.freeze(["r", "q", "p"]),
]);
const BINARY_OPERATORS = Object.freeze(["and", "or", "implies"]);

const proposition = (name) => ({ kind: "proposition", name });
const negate = (value) => ({ kind: "not", value });
const binary = (operator, left, right) => ({
  kind: "binary",
  operator,
  left,
  right,
});

const and = (left, right) => binary("and", left, right);
const or = (left, right) => binary("or", left, right);
const implies = (left, right) => binary("implies", left, right);

function bitCount(mask) {
  let count = 0;
  for (let value = mask; value > 0; value >>= 1) count += value & 1;
  return count;
}

function binaryRank(masks) {
  const pivots = [0, 0, 0];
  let rank = 0;
  for (const original of masks) {
    let mask = original;
    for (let bit = 2; bit >= 0; bit -= 1) {
      if ((mask & (1 << bit)) === 0) continue;
      if (pivots[bit] !== 0) {
        mask ^= pivots[bit];
      } else {
        pivots[bit] = mask;
        rank += 1;
        break;
      }
    }
  }
  return rank;
}

function affineBases(maximumWeight) {
  const result = [];
  for (let first = 1; first <= 7; first += 1) {
    for (let second = 1; second <= 7; second += 1) {
      for (let third = 1; third <= 7; third += 1) {
        if (
          Math.max(bitCount(first), bitCount(second), bitCount(third)) <=
            maximumWeight &&
          binaryRank([first, second, third]) === 3
        ) {
          result.push(Object.freeze([first, second, third]));
        }
      }
    }
  }
  return Object.freeze(result);
}

const AFFINE_BASES_BY_COMPLEXITY = Object.freeze({
  1: affineBases(1),
  2: affineBases(2),
});

const premise = (key, formula) => ({ key, formula });
const proofPlan = (id, build) => ({ id, build });

function metricsHint({ lineCount, subproofs, multiSubproofRules, maxDepth, rules }) {
  const distinctRuleIds = [...new Set(rules)];
  return Object.freeze({
    lineCount,
    subproofs,
    multiSubproofRules,
    maxDepth,
    extraDepth: Math.max(0, maxDepth - 1),
    distinctRuleIds: Object.freeze(distinctRuleIds),
    extraDistinctRules: Math.max(0, distinctRuleIds.length - 1),
    derivedRuleIds: Object.freeze(
      distinctRuleIds.filter((id) =>
        [
          "disjunctive-syllogism",
          "modus-tollens",
          "double-negation",
          "excluded-middle",
          "demorgan",
        ].includes(id),
      ),
    ),
  });
}

const CHALLENGE_TEMPLATES = Object.freeze([
  {
    id: "identity-theorem",
    difficultyHint: metricsHint({
      lineCount: 2,
      subproofs: 1,
      multiSubproofRules: 0,
      maxDepth: 1,
      rules: ["assumption", "implies-intro"],
    }),
    make: ({ A }) => {
      const conclusion = implies(A, A);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("identity", ({ add, range }) => {
            const start = add(A, "assumption", "", ["identity"]);
            add(conclusion, "implies-intro", range(start, start));
          }),
        ],
      };
    },
  },
  {
    id: "excluded-middle-theorem",
    difficultyHint: metricsHint({
      lineCount: 3,
      subproofs: 1,
      multiSubproofRules: 0,
      maxDepth: 1,
      rules: ["assumption", "demorgan", "indirect-proof"],
    }),
    make: ({ A }) => {
      const conclusion = or(A, negate(A));
      const contradiction = and(negate(A), negate(negate(A)));
      const directContradiction = and(conclusion, negate(conclusion));
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("demorgan-reductio", ({ add, cite, range }) => {
            const start = add(
              negate(conclusion),
              "assumption",
              "",
              ["excluded-middle"],
            );
            const end = add(
              contradiction,
              "demorgan",
              cite(start),
              ["excluded-middle"],
            );
            add(conclusion, "indirect-proof", range(start, end));
          }),
        ],
        basicPlans: [
          proofPlan("basic-excluded-middle", ({ add, cite, range }) => {
            const outerStart = add(
              negate(conclusion),
              "assumption",
              "",
              ["basic-lem"],
            );
            const innerStart = add(
              A,
              "assumption",
              "",
              ["basic-lem", "basic-lem-a"],
            );
            const firstDisjunction = add(
              conclusion,
              "or-intro",
              cite(innerStart),
              ["basic-lem", "basic-lem-a"],
            );
            const innerEnd = add(
              directContradiction,
              "and-intro",
              cite(firstDisjunction, outerStart),
              ["basic-lem", "basic-lem-a"],
            );
            const notA = add(
              negate(A),
              "not-intro",
              range(innerStart, innerEnd),
              ["basic-lem"],
            );
            const secondDisjunction = add(
              conclusion,
              "or-intro",
              cite(notA),
              ["basic-lem"],
            );
            const outerEnd = add(
              directContradiction,
              "and-intro",
              cite(secondDisjunction, outerStart),
              ["basic-lem"],
            );
            add(conclusion, "indirect-proof", range(outerStart, outerEnd));
          }),
        ],
      };
    },
  },
  {
    id: "conjunction-commutation-theorem",
    difficultyHint: metricsHint({
      lineCount: 5,
      subproofs: 1,
      multiSubproofRules: 0,
      maxDepth: 1,
      rules: ["assumption", "and-elim", "and-intro", "implies-intro"],
    }),
    make: ({ A, B }) => {
      const source = and(A, B);
      const result = and(B, A);
      const conclusion = implies(source, result);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("commute-conjunction", ({ add, cite, range }) => {
            const start = add(source, "assumption", "", ["commutation"]);
            const left = add(A, "and-elim", cite(start), ["commutation"]);
            const right = add(B, "and-elim", cite(start), ["commutation"]);
            const end = add(
              result,
              "and-intro",
              cite(right, left),
              ["commutation"],
            );
            add(conclusion, "implies-intro", range(start, end));
          }),
        ],
      };
    },
  },
  {
    id: "contraposition-theorem",
    difficultyHint: metricsHint({
      lineCount: 5,
      subproofs: 2,
      multiSubproofRules: 0,
      maxDepth: 2,
      rules: ["assumption", "modus-tollens", "implies-intro"],
    }),
    make: ({ A, B }) => {
      const conditional = implies(A, B);
      const inner = implies(negate(B), negate(A));
      const conclusion = implies(conditional, inner);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("nested-contraposition", ({ add, cite, range }) => {
            const outerStart = add(
              conditional,
              "assumption",
              "",
              ["contraposition-outer"],
            );
            const innerStart = add(
              negate(B),
              "assumption",
              "",
              ["contraposition-outer", "contraposition-inner"],
            );
            const innerEnd = add(
              negate(A),
              "modus-tollens",
              cite(outerStart, innerStart),
              ["contraposition-outer", "contraposition-inner"],
            );
            const outerEnd = add(
              inner,
              "implies-intro",
              range(innerStart, innerEnd),
              ["contraposition-outer"],
            );
            add(conclusion, "implies-intro", range(outerStart, outerEnd));
          }),
        ],
        basicPlans: [
          proofPlan("basic-contraposition", ({ add, cite, range }) => {
            const outerStart = add(
              conditional,
              "assumption",
              "",
              ["basic-contraposition"],
            );
            const innerStart = add(
              negate(B),
              "assumption",
              "",
              ["basic-contraposition", "basic-contraposition-not-b"],
            );
            const aStart = add(
              A,
              "assumption",
              "",
              [
                "basic-contraposition",
                "basic-contraposition-not-b",
                "basic-contraposition-a",
              ],
            );
            const bLine = add(
              B,
              "implies-elim",
              cite(outerStart, aStart),
              [
                "basic-contraposition",
                "basic-contraposition-not-b",
                "basic-contraposition-a",
              ],
            );
            const contradictionLine = add(
              and(B, negate(B)),
              "and-intro",
              cite(bLine, innerStart),
              [
                "basic-contraposition",
                "basic-contraposition-not-b",
                "basic-contraposition-a",
              ],
            );
            const notA = add(
              negate(A),
              "not-intro",
              range(aStart, contradictionLine),
              ["basic-contraposition", "basic-contraposition-not-b"],
            );
            const innerEnd = add(
              inner,
              "implies-intro",
              range(innerStart, notA),
              ["basic-contraposition"],
            );
            add(conclusion, "implies-intro", range(outerStart, innerEnd));
          }),
        ],
      };
    },
  },
  {
    id: "conjunction-introduction",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["and-intro"],
    }),
    make: ({ A, B }) => {
      const conclusion = and(A, B);
      return {
        premises: [premise("A", A), premise("B", B)],
        conclusion,
        plans: [
          proofPlan("direct-and-intro", ({ add, cite, premiseNumber }) => {
            add(
              conclusion,
              "and-intro",
              cite(premiseNumber("A"), premiseNumber("B")),
            );
          }),
        ],
      };
    },
  },
  {
    id: "conjunction-elimination",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["and-elim"],
    }),
    make: ({ A, B }, random) => {
      const source = and(A, B);
      const conclusion = randomUnit(random) < 0.5 ? A : B;
      return {
        premises: [premise("source", source)],
        conclusion,
        plans: [
          proofPlan("direct-and-elim", ({ add, cite, premiseNumber }) => {
            add(conclusion, "and-elim", cite(premiseNumber("source")));
          }),
        ],
      };
    },
  },
  {
    id: "disjunction-introduction",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["or-intro"],
    }),
    make: ({ A, B }, random) => {
      const conclusion = randomUnit(random) < 0.5 ? or(A, B) : or(B, A);
      return {
        premises: [premise("A", A)],
        conclusion,
        plans: [
          proofPlan("direct-or-intro", ({ add, cite, premiseNumber }) => {
            add(conclusion, "or-intro", cite(premiseNumber("A")));
          }),
        ],
      };
    },
  },
  {
    id: "modus-ponens",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["implies-elim"],
    }),
    make: ({ A, B }) => {
      const conditional = implies(A, B);
      return {
        premises: [premise("conditional", conditional), premise("A", A)],
        conclusion: B,
        plans: [
          proofPlan("direct-modus-ponens", ({ add, cite, premiseNumber }) => {
            add(
              B,
              "implies-elim",
              cite(premiseNumber("conditional"), premiseNumber("A")),
            );
          }),
        ],
      };
    },
  },
  {
    id: "modus-tollens",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["modus-tollens"],
    }),
    make: ({ A, B }) => {
      const conditional = implies(A, B);
      const notB = negate(B);
      return {
        premises: [
          premise("conditional", conditional),
          premise("notB", notB),
        ],
        conclusion: negate(A),
        plans: [
          proofPlan("direct-modus-tollens", ({ add, cite, premiseNumber }) => {
            add(
              negate(A),
              "modus-tollens",
              cite(premiseNumber("conditional"), premiseNumber("notB")),
            );
          }),
        ],
        basicPlans: [
          proofPlan(
            "basic-modus-tollens",
            ({ add, cite, premiseNumber, range }) => {
              const start = add(A, "assumption", "", ["basic-mt"]);
              const bLine = add(
                B,
                "implies-elim",
                cite(premiseNumber("conditional"), start),
                ["basic-mt"],
              );
              const end = add(
                and(B, negate(B)),
                "and-intro",
                cite(bLine, premiseNumber("notB")),
                ["basic-mt"],
              );
              add(negate(A), "not-intro", range(start, end));
            },
          ),
        ],
      };
    },
  },
  {
    id: "hypothetical-syllogism",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 4,
      subproofs: 1,
      multiSubproofRules: 0,
      maxDepth: 1,
      rules: ["assumption", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const first = implies(A, B);
      const second = implies(B, C);
      const conclusion = implies(A, C);
      return {
        premises: [premise("first", first), premise("second", second)],
        conclusion,
        plans: [
          proofPlan(
            "chain-conditionals",
            ({ add, cite, premiseNumber, range }) => {
              const start = add(A, "assumption", "", ["hypothetical"]);
              const middle = add(
                B,
                "implies-elim",
                cite(premiseNumber("first"), start),
                ["hypothetical"],
              );
              const end = add(
                C,
                "implies-elim",
                cite(premiseNumber("second"), middle),
                ["hypothetical"],
              );
              add(conclusion, "implies-intro", range(start, end));
            },
          ),
        ],
      };
    },
  },
  {
    id: "disjunctive-syllogism",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["disjunctive-syllogism"],
    }),
    make: ({ A, B }) => {
      const disjunction = or(A, B);
      const notA = negate(A);
      return {
        premises: [
          premise("disjunction", disjunction),
          premise("notA", notA),
        ],
        conclusion: B,
        plans: [
          proofPlan(
            "direct-disjunctive-syllogism",
            ({ add, cite, premiseNumber }) => {
              add(
                B,
                "disjunctive-syllogism",
                cite(premiseNumber("disjunction"), premiseNumber("notA")),
              );
            },
          ),
        ],
        basicPlans: [
          proofPlan("basic-disjunctive-syllogism", ({ add, cite, premiseNumber, range }) => {
            const leftStart = add(A, "assumption", "", ["basic-ds-left"]);
            const contradictionLine = add(
              and(A, negate(A)),
              "and-intro",
              cite(leftStart, premiseNumber("notA")),
              ["basic-ds-left"],
            );
            const reductioStart = add(
              negate(B),
              "assumption",
              "",
              ["basic-ds-left", "basic-ds-ip"],
            );
            const reductioEnd = add(
              and(A, negate(A)),
              "reiteration",
              cite(contradictionLine),
              ["basic-ds-left", "basic-ds-ip"],
            );
            const leftEnd = add(
              B,
              "indirect-proof",
              range(reductioStart, reductioEnd),
              ["basic-ds-left"],
            );
            const rightStart = add(B, "assumption", "", ["basic-ds-right"]);
            add(
              B,
              "or-elim",
              cite(
                premiseNumber("disjunction"),
                range(leftStart, leftEnd),
                range(rightStart, rightStart),
              ),
            );
          }),
        ],
      };
    },
  },
  {
    id: "proof-by-cases",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 5,
      subproofs: 2,
      multiSubproofRules: 1,
      maxDepth: 1,
      rules: ["assumption", "implies-elim", "or-elim"],
    }),
    make: ({ A, B, C }) => {
      const disjunction = or(A, B);
      const fromA = implies(A, C);
      const fromB = implies(B, C);
      return {
        premises: [
          premise("disjunction", disjunction),
          premise("fromA", fromA),
          premise("fromB", fromB),
        ],
        conclusion: C,
        plans: [
          proofPlan("proof-by-cases", ({ add, cite, premiseNumber, range }) => {
            const leftStart = add(A, "assumption", "", ["cases-left"]);
            const leftEnd = add(
              C,
              "implies-elim",
              cite(premiseNumber("fromA"), leftStart),
              ["cases-left"],
            );
            const rightStart = add(B, "assumption", "", ["cases-right"]);
            const rightEnd = add(
              C,
              "implies-elim",
              cite(premiseNumber("fromB"), rightStart),
              ["cases-right"],
            );
            add(
              C,
              "or-elim",
              cite(
                premiseNumber("disjunction"),
                range(leftStart, leftEnd),
                range(rightStart, rightEnd),
              ),
            );
          }),
        ],
      };
    },
  },
  {
    id: "demorgan",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["demorgan"],
    }),
    make: ({ A, B }) => {
      const source = negate(or(A, B));
      const conclusion = and(negate(A), negate(B));
      return {
        premises: [premise("source", source)],
        conclusion,
        plans: [
          proofPlan("direct-demorgan", ({ add, cite, premiseNumber }) => {
            add(conclusion, "demorgan", cite(premiseNumber("source")));
          }),
        ],
        basicPlans: [
          proofPlan("basic-demorgan", ({ add, cite, premiseNumber, range }) => {
            const leftStart = add(A, "assumption", "", ["basic-demorgan-a"]);
            const leftDisjunction = add(
              or(A, B),
              "or-intro",
              cite(leftStart),
              ["basic-demorgan-a"],
            );
            const leftEnd = add(
              and(or(A, B), source),
              "and-intro",
              cite(leftDisjunction, premiseNumber("source")),
              ["basic-demorgan-a"],
            );
            const notA = add(
              negate(A),
              "not-intro",
              range(leftStart, leftEnd),
            );
            const rightStart = add(B, "assumption", "", ["basic-demorgan-b"]);
            const rightDisjunction = add(
              or(A, B),
              "or-intro",
              cite(rightStart),
              ["basic-demorgan-b"],
            );
            const rightEnd = add(
              and(or(A, B), source),
              "and-intro",
              cite(rightDisjunction, premiseNumber("source")),
              ["basic-demorgan-b"],
            );
            const notB = add(
              negate(B),
              "not-intro",
              range(rightStart, rightEnd),
            );
            add(conclusion, "and-intro", cite(notA, notB));
          }),
        ],
      };
    },
  },
  {
    id: "double-negation",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 1,
      subproofs: 0,
      multiSubproofRules: 0,
      maxDepth: 0,
      rules: ["double-negation"],
    }),
    make: ({ A }) => {
      const source = negate(negate(A));
      return {
        premises: [premise("source", source)],
        conclusion: A,
        plans: [
          proofPlan("direct-double-negation", ({ add, cite, premiseNumber }) => {
            add(A, "double-negation", cite(premiseNumber("source")));
          }),
        ],
        basicPlans: [
          proofPlan("basic-double-negation", ({ add, cite, premiseNumber, range }) => {
            const start = add(negate(A), "assumption", "", ["basic-dne"]);
            const end = add(
              and(negate(A), source),
              "and-intro",
              cite(start, premiseNumber("source")),
              ["basic-dne"],
            );
            add(A, "indirect-proof", range(start, end));
          }),
        ],
      };
    },
  },
  {
    id: "conditional-conjunction",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 5,
      subproofs: 1,
      multiSubproofRules: 0,
      maxDepth: 1,
      rules: ["assumption", "implies-elim", "and-intro", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const toB = implies(A, B);
      const toC = implies(A, C);
      const conjunction = and(B, C);
      const conclusion = implies(A, conjunction);
      return {
        premises: [premise("toB", toB), premise("toC", toC)],
        conclusion,
        plans: [
          proofPlan(
            "conditional-conjunction",
            ({ add, cite, premiseNumber, range }) => {
              const start = add(A, "assumption", "", ["conditional-and"]);
              const left = add(
                B,
                "implies-elim",
                cite(premiseNumber("toB"), start),
                ["conditional-and"],
              );
              const right = add(
                C,
                "implies-elim",
                cite(premiseNumber("toC"), start),
                ["conditional-and"],
              );
              const end = add(
                conjunction,
                "and-intro",
                cite(left, right),
                ["conditional-and"],
              );
              add(conclusion, "implies-intro", range(start, end));
            },
          ),
        ],
      };
    },
  },
  {
    id: "conditional-disjunction",
    weight: 2,
    difficultyHint: metricsHint({
      lineCount: 7,
      subproofs: 3,
      multiSubproofRules: 1,
      maxDepth: 2,
      rules: ["assumption", "implies-elim", "or-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const fromA = implies(A, C);
      const fromB = implies(B, C);
      const disjunction = or(A, B);
      const conclusion = implies(disjunction, C);
      return {
        premises: [premise("fromA", fromA), premise("fromB", fromB)],
        conclusion,
        plans: [
          proofPlan(
            "conditional-disjunction",
            ({ add, cite, premiseNumber, range }) => {
              const outerStart = add(
                disjunction,
                "assumption",
                "",
                ["conditional-or"],
              );
              const leftStart = add(
                A,
                "assumption",
                "",
                ["conditional-or", "conditional-or-left"],
              );
              const leftEnd = add(
                C,
                "implies-elim",
                cite(premiseNumber("fromA"), leftStart),
                ["conditional-or", "conditional-or-left"],
              );
              const rightStart = add(
                B,
                "assumption",
                "",
                ["conditional-or", "conditional-or-right"],
              );
              const rightEnd = add(
                C,
                "implies-elim",
                cite(premiseNumber("fromB"), rightStart),
                ["conditional-or", "conditional-or-right"],
              );
              const outerEnd = add(
                C,
                "or-elim",
                cite(
                  outerStart,
                  range(leftStart, leftEnd),
                  range(rightStart, rightEnd),
                ),
                ["conditional-or"],
              );
              add(conclusion, "implies-intro", range(outerStart, outerEnd));
            },
          ),
        ],
      };
    },
  },
  {
    id: "peirce-law",
    advanced: true,
    recognizable: true,
    weight: 8,
    difficultyHint: metricsHint({
      lineCount: 10,
      subproofs: 3,
      multiSubproofRules: 0,
      maxDepth: 3,
      rules: [
        "assumption",
        "and-intro",
        "disjunctive-syllogism",
        "indirect-proof",
        "or-intro",
        "implies-intro",
        "implies-elim",
      ],
    }),
    make: ({ A, B }) => {
      const conditional = implies(A, B);
      const hypothesis = implies(conditional, A);
      const conclusion = implies(hypothesis, A);
      const contradiction = and(A, negate(A));
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("peirce-derived", ({ add, cite, range }) => {
            const outerStart = add(
              hypothesis,
              "assumption",
              "",
              ["peirce"],
            );
            const reductioStart = add(
              negate(A),
              "assumption",
              "",
              ["peirce", "not-a"],
            );
            const conditionalStart = add(
              A,
              "assumption",
              "",
              ["peirce", "not-a", "conditional"],
            );
            const disjunction = add(
              or(A, B),
              "or-intro",
              cite(conditionalStart),
              ["peirce", "not-a", "conditional"],
            );
            const bLine = add(
              B,
              "disjunctive-syllogism",
              cite(disjunction, reductioStart),
              ["peirce", "not-a", "conditional"],
            );
            const conditionalLine = add(
              conditional,
              "implies-intro",
              range(conditionalStart, bLine),
              ["peirce", "not-a"],
            );
            const aLine = add(
              A,
              "implies-elim",
              cite(outerStart, conditionalLine),
              ["peirce", "not-a"],
            );
            const reductioEnd = add(
              contradiction,
              "and-intro",
              cite(aLine, reductioStart),
              ["peirce", "not-a"],
            );
            const aByReductio = add(
              A,
              "indirect-proof",
              range(reductioStart, reductioEnd),
              ["peirce"],
            );
            add(
              conclusion,
              "implies-intro",
              range(outerStart, aByReductio),
            );
          }),
        ],
        basicPlans: [
          proofPlan("peirce-basic-reductio", ({ add, cite, range }) => {
            const outerStart = add(hypothesis, "assumption", "", ["peirce"]);
            const reductioStart = add(
              negate(A),
              "assumption",
              "",
              ["peirce", "not-a"],
            );
            const conditionalStart = add(
              A,
              "assumption",
              "",
              ["peirce", "not-a", "conditional"],
            );
            const bReductioStart = add(
              negate(B),
              "assumption",
              "",
              ["peirce", "not-a", "conditional", "not-b"],
            );
            const bReductioEnd = add(
              contradiction,
              "and-intro",
              cite(conditionalStart, reductioStart),
              ["peirce", "not-a", "conditional", "not-b"],
            );
            const bLine = add(
              B,
              "indirect-proof",
              range(bReductioStart, bReductioEnd),
              ["peirce", "not-a", "conditional"],
            );
            const conditionalLine = add(
              conditional,
              "implies-intro",
              range(conditionalStart, bLine),
              ["peirce", "not-a"],
            );
            const aLine = add(
              A,
              "implies-elim",
              cite(outerStart, conditionalLine),
              ["peirce", "not-a"],
            );
            const reductioEnd = add(
              contradiction,
              "and-intro",
              cite(aLine, reductioStart),
              ["peirce", "not-a"],
            );
            const aByReductio = add(
              A,
              "indirect-proof",
              range(reductioStart, reductioEnd),
              ["peirce"],
            );
            add(
              conclusion,
              "implies-intro",
              range(outerStart, aByReductio),
            );
          }),
        ],
      };
    },
  },
  {
    id: "implication-distribution-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 9,
      subproofs: 3,
      multiSubproofRules: 0,
      maxDepth: 3,
      rules: ["assumption", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const source = implies(A, implies(B, C));
      const fromA = implies(A, B);
      const toC = implies(A, C);
      const middle = implies(fromA, toC);
      const conclusion = implies(source, middle);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("implication-distribution", ({ add, cite, range }) => {
            const outerStart = add(source, "assumption", "", ["distribution"]);
            const middleStart = add(
              fromA,
              "assumption",
              "",
              ["distribution", "from-a"],
            );
            const innerStart = add(
              A,
              "assumption",
              "",
              ["distribution", "from-a", "a"],
            );
            const fromB = add(
              implies(B, C),
              "implies-elim",
              cite(outerStart, innerStart),
              ["distribution", "from-a", "a"],
            );
            const bLine = add(
              B,
              "implies-elim",
              cite(middleStart, innerStart),
              ["distribution", "from-a", "a"],
            );
            const cLine = add(
              C,
              "implies-elim",
              cite(fromB, bLine),
              ["distribution", "from-a", "a"],
            );
            const innerEnd = add(
              toC,
              "implies-intro",
              range(innerStart, cLine),
              ["distribution", "from-a"],
            );
            const middleEnd = add(
              middle,
              "implies-intro",
              range(middleStart, innerEnd),
              ["distribution"],
            );
            add(conclusion, "implies-intro", range(outerStart, middleEnd));
          }),
        ],
      };
    },
  },
  {
    id: "implication-exchange-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 8,
      subproofs: 3,
      multiSubproofRules: 0,
      maxDepth: 3,
      rules: ["assumption", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const source = implies(A, implies(B, C));
      const inner = implies(A, C);
      const exchanged = implies(B, inner);
      const conclusion = implies(source, exchanged);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("implication-exchange", ({ add, cite, range }) => {
            const outerStart = add(source, "assumption", "", ["exchange"]);
            const middleStart = add(
              B,
              "assumption",
              "",
              ["exchange", "b"],
            );
            const innerStart = add(
              A,
              "assumption",
              "",
              ["exchange", "b", "a"],
            );
            const fromB = add(
              implies(B, C),
              "implies-elim",
              cite(outerStart, innerStart),
              ["exchange", "b", "a"],
            );
            const cLine = add(
              C,
              "implies-elim",
              cite(fromB, middleStart),
              ["exchange", "b", "a"],
            );
            const innerEnd = add(
              inner,
              "implies-intro",
              range(innerStart, cLine),
              ["exchange", "b"],
            );
            const middleEnd = add(
              exchanged,
              "implies-intro",
              range(middleStart, innerEnd),
              ["exchange"],
            );
            add(conclusion, "implies-intro", range(outerStart, middleEnd));
          }),
        ],
      };
    },
  },
  {
    id: "implication-composition-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 8,
      subproofs: 3,
      multiSubproofRules: 0,
      maxDepth: 3,
      rules: ["assumption", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const toC = implies(B, C);
      const toB = implies(A, B);
      const result = implies(A, C);
      const middle = implies(toB, result);
      const conclusion = implies(toC, middle);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("implication-composition", ({ add, cite, range }) => {
            const outerStart = add(toC, "assumption", "", ["composition"]);
            const middleStart = add(
              toB,
              "assumption",
              "",
              ["composition", "to-b"],
            );
            const innerStart = add(
              A,
              "assumption",
              "",
              ["composition", "to-b", "a"],
            );
            const bLine = add(
              B,
              "implies-elim",
              cite(middleStart, innerStart),
              ["composition", "to-b", "a"],
            );
            const cLine = add(
              C,
              "implies-elim",
              cite(outerStart, bLine),
              ["composition", "to-b", "a"],
            );
            const innerEnd = add(
              result,
              "implies-intro",
              range(innerStart, cLine),
              ["composition", "to-b"],
            );
            const middleEnd = add(
              middle,
              "implies-intro",
              range(middleStart, innerEnd),
              ["composition"],
            );
            add(conclusion, "implies-intro", range(outerStart, middleEnd));
          }),
        ],
      };
    },
  },
  {
    id: "exportation-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 8,
      subproofs: 3,
      multiSubproofRules: 0,
      maxDepth: 3,
      rules: ["assumption", "and-intro", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const paired = and(A, B);
      const source = implies(paired, C);
      const inner = implies(B, C);
      const exported = implies(A, inner);
      const conclusion = implies(source, exported);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("exportation", ({ add, cite, range }) => {
            const outerStart = add(source, "assumption", "", ["exportation"]);
            const middleStart = add(
              A,
              "assumption",
              "",
              ["exportation", "a"],
            );
            const innerStart = add(
              B,
              "assumption",
              "",
              ["exportation", "a", "b"],
            );
            const pairLine = add(
              paired,
              "and-intro",
              cite(middleStart, innerStart),
              ["exportation", "a", "b"],
            );
            const cLine = add(
              C,
              "implies-elim",
              cite(outerStart, pairLine),
              ["exportation", "a", "b"],
            );
            const innerEnd = add(
              inner,
              "implies-intro",
              range(innerStart, cLine),
              ["exportation", "a"],
            );
            const middleEnd = add(
              exported,
              "implies-intro",
              range(middleStart, innerEnd),
              ["exportation"],
            );
            add(conclusion, "implies-intro", range(outerStart, middleEnd));
          }),
        ],
      };
    },
  },
  {
    id: "importation-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 8,
      subproofs: 2,
      multiSubproofRules: 0,
      maxDepth: 2,
      rules: ["assumption", "and-elim", "implies-elim", "implies-intro"],
    }),
    make: ({ A, B, C }) => {
      const source = implies(A, implies(B, C));
      const paired = and(A, B);
      const imported = implies(paired, C);
      const conclusion = implies(source, imported);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("importation", ({ add, cite, range }) => {
            const outerStart = add(source, "assumption", "", ["importation"]);
            const innerStart = add(
              paired,
              "assumption",
              "",
              ["importation", "pair"],
            );
            const aLine = add(
              A,
              "and-elim",
              cite(innerStart),
              ["importation", "pair"],
            );
            const bLine = add(
              B,
              "and-elim",
              cite(innerStart),
              ["importation", "pair"],
            );
            const fromB = add(
              implies(B, C),
              "implies-elim",
              cite(outerStart, aLine),
              ["importation", "pair"],
            );
            const cLine = add(
              C,
              "implies-elim",
              cite(fromB, bLine),
              ["importation", "pair"],
            );
            const innerEnd = add(
              imported,
              "implies-intro",
              range(innerStart, cLine),
              ["importation"],
            );
            add(conclusion, "implies-intro", range(outerStart, innerEnd));
          }),
        ],
      };
    },
  },
  {
    id: "bundled-dilemma-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 11,
      subproofs: 4,
      multiSubproofRules: 1,
      maxDepth: 3,
      rules: [
        "assumption",
        "and-elim",
        "implies-elim",
        "or-elim",
        "implies-intro",
      ],
    }),
    make: ({ A, B, C }) => {
      const fromA = implies(A, B);
      const fromC = implies(C, B);
      const paired = and(fromA, fromC);
      const cases = or(A, C);
      const conditional = implies(cases, B);
      const conclusion = implies(paired, conditional);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("bundled-dilemma", ({ add, cite, range }) => {
            const outerStart = add(paired, "assumption", "", ["dilemma"]);
            const fromALine = add(
              fromA,
              "and-elim",
              cite(outerStart),
              ["dilemma"],
            );
            const fromCLine = add(
              fromC,
              "and-elim",
              cite(outerStart),
              ["dilemma"],
            );
            const conditionalStart = add(
              cases,
              "assumption",
              "",
              ["dilemma", "cases"],
            );
            const leftStart = add(
              A,
              "assumption",
              "",
              ["dilemma", "cases", "left"],
            );
            const leftEnd = add(
              B,
              "implies-elim",
              cite(fromALine, leftStart),
              ["dilemma", "cases", "left"],
            );
            const rightStart = add(
              C,
              "assumption",
              "",
              ["dilemma", "cases", "right"],
            );
            const rightEnd = add(
              B,
              "implies-elim",
              cite(fromCLine, rightStart),
              ["dilemma", "cases", "right"],
            );
            const casesEnd = add(
              B,
              "or-elim",
              cite(
                conditionalStart,
                range(leftStart, leftEnd),
                range(rightStart, rightEnd),
              ),
              ["dilemma", "cases"],
            );
            const conditionalEnd = add(
              conditional,
              "implies-intro",
              range(conditionalStart, casesEnd),
              ["dilemma"],
            );
            add(
              conclusion,
              "implies-intro",
              range(outerStart, conditionalEnd),
            );
          }),
        ],
      };
    },
  },
  {
    id: "linearity-theorem",
    advanced: true,
    recognizable: true,
    difficultyHint: metricsHint({
      lineCount: 12,
      subproofs: 4,
      multiSubproofRules: 1,
      maxDepth: 2,
      rules: [
        "assumption",
        "reiteration",
        "implies-intro",
        "or-intro",
        "disjunctive-syllogism",
        "excluded-middle",
      ],
    }),
    make: ({ A, B }) => {
      const aToB = implies(A, B);
      const bToA = implies(B, A);
      const conclusion = or(aToB, bToA);
      const contradiction = and(conclusion, negate(conclusion));
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("linearity-derived", ({ add, cite, range }) => {
            const aStart = add(A, "assumption", "", ["linearity-a"]);
            const bStart = add(
              B,
              "assumption",
              "",
              ["linearity-a", "b-to-a"],
            );
            const aAgain = add(
              A,
              "reiteration",
              cite(aStart),
              ["linearity-a", "b-to-a"],
            );
            const bToALine = add(
              bToA,
              "implies-intro",
              range(bStart, aAgain),
              ["linearity-a"],
            );
            const leftEnd = add(
              conclusion,
              "or-intro",
              cite(bToALine),
              ["linearity-a"],
            );
            const notAStart = add(
              negate(A),
              "assumption",
              "",
              ["linearity-not-a"],
            );
            const aForConditional = add(
              A,
              "assumption",
              "",
              ["linearity-not-a", "a-to-b"],
            );
            const aOrB = add(
              or(A, B),
              "or-intro",
              cite(aForConditional),
              ["linearity-not-a", "a-to-b"],
            );
            const bLine = add(
              B,
              "disjunctive-syllogism",
              cite(aOrB, notAStart),
              ["linearity-not-a", "a-to-b"],
            );
            const aToBLine = add(
              aToB,
              "implies-intro",
              range(aForConditional, bLine),
              ["linearity-not-a"],
            );
            const rightEnd = add(
              conclusion,
              "or-intro",
              cite(aToBLine),
              ["linearity-not-a"],
            );
            add(
              conclusion,
              "excluded-middle",
              cite(range(aStart, leftEnd), range(notAStart, rightEnd)),
            );
          }),
        ],
        basicPlans: [
          proofPlan("linearity-basic", ({ add, cite, range }) => {
            const outerStart = add(
              negate(conclusion),
              "assumption",
              "",
              ["linearity-ip"],
            );
            const aStart = add(
              A,
              "assumption",
              "",
              ["linearity-ip", "a-to-b"],
            );
            const bStart = add(
              B,
              "assumption",
              "",
              ["linearity-ip", "a-to-b", "b-to-a"],
            );
            const aAgain = add(
              A,
              "reiteration",
              cite(aStart),
              ["linearity-ip", "a-to-b", "b-to-a"],
            );
            const bToALine = add(
              bToA,
              "implies-intro",
              range(bStart, aAgain),
              ["linearity-ip", "a-to-b"],
            );
            const disjunctionFromRight = add(
              conclusion,
              "or-intro",
              cite(bToALine),
              ["linearity-ip", "a-to-b"],
            );
            const notBStart = add(
              negate(B),
              "assumption",
              "",
              ["linearity-ip", "a-to-b", "not-b"],
            );
            const innerEnd = add(
              contradiction,
              "and-intro",
              cite(disjunctionFromRight, outerStart),
              ["linearity-ip", "a-to-b", "not-b"],
            );
            const bLine = add(
              B,
              "indirect-proof",
              range(notBStart, innerEnd),
              ["linearity-ip", "a-to-b"],
            );
            const aToBLine = add(
              aToB,
              "implies-intro",
              range(aStart, bLine),
              ["linearity-ip"],
            );
            const disjunctionFromLeft = add(
              conclusion,
              "or-intro",
              cite(aToBLine),
              ["linearity-ip"],
            );
            const outerEnd = add(
              contradiction,
              "and-intro",
              cite(disjunctionFromLeft, outerStart),
              ["linearity-ip"],
            );
            add(
              conclusion,
              "indirect-proof",
              range(outerStart, outerEnd),
            );
          }),
        ],
      };
    },
  },
  {
    id: "tarski-law",
    advanced: true,
    recognizable: true,
    difficultyHint: metricsHint({
      lineCount: 9,
      subproofs: 3,
      multiSubproofRules: 1,
      maxDepth: 2,
      rules: [
        "assumption",
        "implies-intro",
        "or-intro",
        "disjunctive-syllogism",
        "excluded-middle",
      ],
    }),
    make: ({ A, B }) => {
      const aToB = implies(A, B);
      const conclusion = or(A, aToB);
      const contradiction = and(conclusion, negate(conclusion));
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("tarski-derived", ({ add, cite, range }) => {
            const aStart = add(A, "assumption", "", ["tarski-a"]);
            const leftEnd = add(
              conclusion,
              "or-intro",
              cite(aStart),
              ["tarski-a"],
            );
            const notAStart = add(
              negate(A),
              "assumption",
              "",
              ["tarski-not-a"],
            );
            const aForConditional = add(
              A,
              "assumption",
              "",
              ["tarski-not-a", "a-to-b"],
            );
            const aOrB = add(
              or(A, B),
              "or-intro",
              cite(aForConditional),
              ["tarski-not-a", "a-to-b"],
            );
            const bLine = add(
              B,
              "disjunctive-syllogism",
              cite(aOrB, notAStart),
              ["tarski-not-a", "a-to-b"],
            );
            const aToBLine = add(
              aToB,
              "implies-intro",
              range(aForConditional, bLine),
              ["tarski-not-a"],
            );
            const rightEnd = add(
              conclusion,
              "or-intro",
              cite(aToBLine),
              ["tarski-not-a"],
            );
            add(
              conclusion,
              "excluded-middle",
              cite(range(aStart, leftEnd), range(notAStart, rightEnd)),
            );
          }),
        ],
        basicPlans: [
          proofPlan("tarski-basic", ({ add, cite, range }) => {
            const outerStart = add(
              negate(conclusion),
              "assumption",
              "",
              ["tarski-ip"],
            );
            const aStart = add(
              A,
              "assumption",
              "",
              ["tarski-ip", "a-to-b"],
            );
            const disjunctionFromA = add(
              conclusion,
              "or-intro",
              cite(aStart),
              ["tarski-ip", "a-to-b"],
            );
            const notBStart = add(
              negate(B),
              "assumption",
              "",
              ["tarski-ip", "a-to-b", "not-b"],
            );
            const innerEnd = add(
              contradiction,
              "and-intro",
              cite(disjunctionFromA, outerStart),
              ["tarski-ip", "a-to-b", "not-b"],
            );
            const bLine = add(
              B,
              "indirect-proof",
              range(notBStart, innerEnd),
              ["tarski-ip", "a-to-b"],
            );
            const aToBLine = add(
              aToB,
              "implies-intro",
              range(aStart, bLine),
              ["tarski-ip"],
            );
            const disjunctionFromConditional = add(
              conclusion,
              "or-intro",
              cite(aToBLine),
              ["tarski-ip"],
            );
            const outerEnd = add(
              contradiction,
              "and-intro",
              cite(disjunctionFromConditional, outerStart),
              ["tarski-ip"],
            );
            add(
              conclusion,
              "indirect-proof",
              range(outerStart, outerEnd),
            );
          }),
        ],
      };
    },
  },
  {
    id: "reverse-distributivity-theorem",
    advanced: true,
    difficultyHint: metricsHint({
      lineCount: 12,
      subproofs: 3,
      multiSubproofRules: 1,
      maxDepth: 2,
      rules: [
        "assumption",
        "and-elim",
        "and-intro",
        "or-intro",
        "disjunctive-syllogism",
        "excluded-middle",
        "implies-intro",
      ],
    }),
    make: ({ A, B, C }) => {
      const aOrB = or(A, B);
      const aOrC = or(A, C);
      const hypothesis = and(aOrB, aOrC);
      const bAndC = and(B, C);
      const result = or(A, bAndC);
      const conclusion = implies(hypothesis, result);
      return {
        premises: [],
        conclusion,
        plans: [
          proofPlan("reverse-distributivity-derived", ({ add, cite, range }) => {
            const outerStart = add(
              hypothesis,
              "assumption",
              "",
              ["reverse-distribution"],
            );
            const firstDisjunction = add(
              aOrB,
              "and-elim",
              cite(outerStart),
              ["reverse-distribution"],
            );
            const secondDisjunction = add(
              aOrC,
              "and-elim",
              cite(outerStart),
              ["reverse-distribution"],
            );
            const aStart = add(
              A,
              "assumption",
              "",
              ["reverse-distribution", "a"],
            );
            const leftEnd = add(
              result,
              "or-intro",
              cite(aStart),
              ["reverse-distribution", "a"],
            );
            const notAStart = add(
              negate(A),
              "assumption",
              "",
              ["reverse-distribution", "not-a"],
            );
            const bLine = add(
              B,
              "disjunctive-syllogism",
              cite(firstDisjunction, notAStart),
              ["reverse-distribution", "not-a"],
            );
            const cLine = add(
              C,
              "disjunctive-syllogism",
              cite(secondDisjunction, notAStart),
              ["reverse-distribution", "not-a"],
            );
            const conjunction = add(
              bAndC,
              "and-intro",
              cite(bLine, cLine),
              ["reverse-distribution", "not-a"],
            );
            const rightEnd = add(
              result,
              "or-intro",
              cite(conjunction),
              ["reverse-distribution", "not-a"],
            );
            const distributed = add(
              result,
              "excluded-middle",
              cite(range(aStart, leftEnd), range(notAStart, rightEnd)),
              ["reverse-distribution"],
            );
            add(
              conclusion,
              "implies-intro",
              range(outerStart, distributed),
            );
          }),
        ],
        basicPlans: [
          proofPlan("reverse-distributivity-basic", ({ add, cite, range }) => {
            const outerStart = add(
              hypothesis,
              "assumption",
              "",
              ["reverse-distribution"],
            );
            const firstDisjunction = add(
              aOrB,
              "and-elim",
              cite(outerStart),
              ["reverse-distribution"],
            );
            const secondDisjunction = add(
              aOrC,
              "and-elim",
              cite(outerStart),
              ["reverse-distribution"],
            );
            const aStart = add(
              A,
              "assumption",
              "",
              ["reverse-distribution", "first-a"],
            );
            const firstEnd = add(
              result,
              "or-intro",
              cite(aStart),
              ["reverse-distribution", "first-a"],
            );
            const bStart = add(
              B,
              "assumption",
              "",
              ["reverse-distribution", "first-b"],
            );
            const innerAStart = add(
              A,
              "assumption",
              "",
              ["reverse-distribution", "first-b", "second-a"],
            );
            const innerAEnd = add(
              result,
              "or-intro",
              cite(innerAStart),
              ["reverse-distribution", "first-b", "second-a"],
            );
            const cStart = add(
              C,
              "assumption",
              "",
              ["reverse-distribution", "first-b", "second-c"],
            );
            const conjunction = add(
              bAndC,
              "and-intro",
              cite(bStart, cStart),
              ["reverse-distribution", "first-b", "second-c"],
            );
            const innerCEnd = add(
              result,
              "or-intro",
              cite(conjunction),
              ["reverse-distribution", "first-b", "second-c"],
            );
            const secondCases = add(
              result,
              "or-elim",
              cite(
                secondDisjunction,
                range(innerAStart, innerAEnd),
                range(cStart, innerCEnd),
              ),
              ["reverse-distribution", "first-b"],
            );
            const firstCases = add(
              result,
              "or-elim",
              cite(
                firstDisjunction,
                range(aStart, firstEnd),
                range(bStart, secondCases),
              ),
              ["reverse-distribution"],
            );
            add(
              conclusion,
              "implies-intro",
              range(outerStart, firstCases),
            );
          }),
        ],
      };
    },
  },
]);

export const PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS = Object.freeze(
  CHALLENGE_TEMPLATES.map(({ id }) => id),
);

export const PROPOSITIONAL_ADVANCED_TEMPLATE_IDS = Object.freeze(
  CHALLENGE_TEMPLATES.filter(({ advanced }) => advanced).map(({ id }) => id),
);

export const PROPOSITIONAL_CHALLENGE_TEMPLATE_BANDS = Object.freeze(
  Object.fromEntries(
    CHALLENGE_TEMPLATES.map((template) => [
      template.id,
      classifyDifficulty(template.difficultyHint).band,
    ]),
  ),
);

const ONE_LINE_CACHE = new Map();
const TEMPLATE_POOL_CACHE = new Map();

function sameFormula(left, right) {
  return formatFormula(left) === formatFormula(right);
}

function randomUnit(random) {
  const value = Number(random());
  if (!Number.isFinite(value) || value < 0 || value >= 1) {
    throw new RangeError("随机数函数必须返回 [0, 1) 内的数");
  }
  return value;
}

function pick(values, random) {
  return values[Math.floor(randomUnit(random) * values.length)];
}

function shuffle(values, random) {
  const result = [...values];
  for (let index = result.length - 1; index > 0; index -= 1) {
    const other = Math.floor(randomUnit(random) * (index + 1));
    [result[index], result[other]] = [result[other], result[index]];
  }
  return result;
}

function templateWeight(template) {
  return template.weight ?? 1;
}

function weightedTemplate(templates, random) {
  const totalWeight = templates.reduce(
    (sum, template) => sum + templateWeight(template),
    0,
  );
  let cursor = randomUnit(random) * totalWeight;
  for (const template of templates) {
    cursor -= templateWeight(template);
    if (cursor < 0) return template;
  }
  return templates.at(-1);
}

function growAnchoredFormula(name, names, random, depth) {
  if (depth <= 0) return proposition(name);

  const inner = growAnchoredFormula(name, names, random, depth - 1);
  if (randomUnit(random) < 0.28) return negate(inner);

  const otherNames = names.filter((candidate) => candidate !== name);
  const otherName = pick(otherNames, random);
  let side = proposition(otherName);
  if (depth > 1 && randomUnit(random) < 0.45) {
    const thirdName = pick(
      names.filter((candidate) => candidate !== otherName),
      random,
    );
    side =
      randomUnit(random) < 0.4
        ? negate(side)
        : binary(
            pick(BINARY_OPERATORS, random),
            side,
            proposition(thirdName),
          );
  }

  const operator = pick(BINARY_OPERATORS, random);
  return randomUnit(random) < 0.5
    ? binary(operator, inner, side)
    : binary(operator, side, inner);
}

function decoratedFormula(name, names, random, maxDepth) {
  const depth = Math.floor(randomUnit(random) * (maxDepth + 1));
  return growAnchoredFormula(name, names, random, depth);
}

function atomicMetavariables(random = null) {
  const names = random ? shuffle(ATOM_NAMES, random) : ATOM_NAMES;
  return {
    A: proposition(names[0]),
    B: proposition(names[1]),
    C: proposition(names[2]),
  };
}

function affineMetavariables(random, maxDepth) {
  // A two-atom parity needs depth 2 in this language; at lower caps a signed
  // permutation is the only affine fallback that can honor the contract.
  const complexity = maxDepth < 2 ? 1 : 2;
  const masks = pick(AFFINE_BASES_BY_COMPLEXITY[complexity], random);
  const names = shuffle(ATOM_NAMES, random);
  const formulaForMask = (mask) => {
    const terms = shuffle(
      names
        .filter((_name, index) => (mask & (1 << index)) !== 0)
        .map(proposition),
      random,
    );
    let formula = terms[0];
    let depth = 0;
    if (terms.length === 2) {
      // (P → Q) ∧ (Q → P) is the complement of XOR. Adding a constant bit
      // to an affine coordinate preserves the invertible coefficient matrix.
      formula = and(
        implies(terms[0], terms[1]),
        implies(terms[1], terms[0]),
      );
      depth = 2;
    }
    return depth < maxDepth && randomUnit(random) < 0.5
      ? negate(formula)
      : formula;
  };
  return {
    A: formulaForMask(masks[0]),
    B: formulaForMask(masks[1]),
    C: formulaForMask(masks[2]),
  };
}

function hasUsefulMetavariables(
  formulas,
  { requireIndependence = false } = {},
) {
  if (new Set(formulas.map(formatFormula)).size !== formulas.length) {
    return false;
  }
  const valuations = valuationsFor(formulas);
  const truthVectors = formulas.map((formula) =>
    valuations.map((valuation) =>
      evaluatePropositionalFormula(formula, valuation),
    ),
  );
  if (
    truthVectors.some(
      (values) =>
        values.every(Boolean) || values.every((value) => !value),
    )
  ) {
    return false;
  }
  for (let first = 0; first < formulas.length; first += 1) {
    for (let second = first + 1; second < formulas.length; second += 1) {
      const truthCombinations = new Set(
        truthVectors[first].map(
          (value, index) =>
            `${Number(value)}${Number(truthVectors[second][index])}`,
        ),
      );
      if (
        truthCombinations.size === 2 ||
        (requireIndependence && truthCombinations.size !== 4)
      ) {
        return false;
      }
    }
  }
  if (requireIndependence) {
    const jointCombinations = new Set(
      valuations.map((_valuation, index) =>
        truthVectors.map((values) => Number(values[index])).join(""),
      ),
    );
    // Advanced proof schemas get all eight valuations of A/B/C. This rules
    // out hidden entailments that can create much shorter special cases.
    if (jointCombinations.size !== 8) return false;
  }
  return true;
}

function sampleMetavariables(
  random,
  maxAttempts,
  maxDepth,
  { requireIndependence = false } = {},
) {
  for (let attempt = 0; attempt < maxAttempts; attempt += 1) {
    const names = shuffle(ATOM_NAMES, random);
    const formulas = names.map((name) =>
      decoratedFormula(name, names, random, maxDepth),
    );
    if (hasUsefulMetavariables(formulas, { requireIndependence })) {
      return { A: formulas[0], B: formulas[1], C: formulas[2] };
    }
  }
  if (requireIndependence) {
    // Affine coordinates form an invertible map of p/q/r; at shallow caps this
    // intentionally reduces to a signed permutation of the atoms.
    return affineMetavariables(random, maxDepth);
  }
  return atomicMetavariables();
}

function collectAtoms(formula, target = new Set()) {
  switch (formula.kind) {
    case "proposition":
      target.add(formula.name);
      break;
    case "not":
      collectAtoms(formula.value, target);
      break;
    case "binary":
      collectAtoms(formula.left, target);
      collectAtoms(formula.right, target);
      break;
    default:
      throw new TypeError("测试模式只接受命题公式");
  }
  return target;
}

export function evaluatePropositionalFormula(formula, valuation) {
  switch (formula.kind) {
    case "proposition":
      return Boolean(valuation[formula.name]);
    case "not":
      return !evaluatePropositionalFormula(formula.value, valuation);
    case "binary": {
      const left = evaluatePropositionalFormula(formula.left, valuation);
      const right = evaluatePropositionalFormula(formula.right, valuation);
      switch (formula.operator) {
        case "and":
          return left && right;
        case "or":
          return left || right;
        case "implies":
          return !left || right;
        case "iff":
          return left === right;
        default:
          throw new TypeError(`未知命题联结词：${formula.operator}`);
      }
    }
    default:
      throw new TypeError("测试模式只接受命题公式");
  }
}

function valuationsFor(formulas) {
  const names = [...formulas.reduce(
    (target, formula) => collectAtoms(formula, target),
    new Set(),
  )].sort();
  return Array.from({ length: 2 ** names.length }, (_unused, index) =>
    Object.fromEntries(
      names.map((name, bit) => [name, Boolean(index & (1 << bit))]),
    ),
  );
}

export function isSatisfiablePropositionalSet(formulas) {
  return valuationsFor(formulas).some((valuation) =>
    formulas.every((formula) => evaluatePropositionalFormula(formula, valuation)),
  );
}

export function isValidPropositionalArgument(premises, conclusion) {
  return valuationsFor([...premises, conclusion]).every(
    (valuation) =>
      !premises.every((premiseFormula) =>
        evaluatePropositionalFormula(premiseFormula, valuation),
      ) || evaluatePropositionalFormula(conclusion, valuation),
  );
}

function hasCleanSemantics(premises, conclusion) {
  if (premises.some((formula) => sameFormula(formula, conclusion))) return false;

  const valuations = valuationsFor([...premises, conclusion]);
  const premiseTruthVectors = premises.map((formula) =>
    valuations.map((valuation) =>
      evaluatePropositionalFormula(formula, valuation),
    ),
  );
  const conclusionTruthVector = valuations.map((valuation) =>
    evaluatePropositionalFormula(conclusion, valuation),
  );
  const allPremisesTrue = valuations.map((_valuation, valuationIndex) =>
    premiseTruthVectors.every((values) => values[valuationIndex]),
  );
  if (!allPremisesTrue.some(Boolean)) return false;
  if (
    allPremisesTrue.some(
      (premisesTrue, index) => premisesTrue && !conclusionTruthVector[index],
    )
  ) {
    return false;
  }
  for (let first = 0; first < premises.length; first += 1) {
    for (let second = first + 1; second < premises.length; second += 1) {
      if (
        premiseTruthVectors[first].every(
          (value, index) => value === premiseTruthVectors[second][index],
        )
      ) {
        return false;
      }
    }
  }
  if (premises.length > 0) {
    if (conclusionTruthVector.every(Boolean)) return false;
    for (let index = 0; index < premises.length; index += 1) {
      const premiseIsEssential = valuations.some(
        (_valuation, valuationIndex) =>
          !conclusionTruthVector[valuationIndex] &&
          premiseTruthVectors.every(
            (values, premiseIndex) =>
              premiseIndex === index || values[valuationIndex],
          ),
      );
      if (!premiseIsEssential) return false;
    }
  }
  return true;
}

function instantiatePlan(plan, premiseEntries) {
  const lines = [];
  const premiseNumbers = new Map(
    premiseEntries.map(({ key }, index) => [key, index + 1]),
  );
  const add = (formula, rule, citations = "", path = []) => {
    const isAssumption = rule === "assumption";
    lines.push({
      formula: formatFormula(formula),
      rule,
      citations,
      path: [...path],
      isAssumption,
    });
    return premiseEntries.length + lines.length;
  };
  plan.build({
    add,
    cite: (...references) => references.join(", "),
    premiseNumber: (key) => {
      if (!premiseNumbers.has(key)) {
        throw new Error(`证明计划引用了未知前提：${key}`);
      }
      return premiseNumbers.get(key);
    },
    range: (start, end) => `${start}-${end}`,
  });
  return lines;
}

function chooseValidatedPlan(
  instance,
  premiseEntries,
  policy,
  { basicOnly = false } = {},
) {
  const premises = premiseEntries.map(({ formula }) => formatFormula(formula));
  const conclusion = formatFormula(instance.conclusion);
  let best = null;
  const plans = basicOnly
    ? (instance.basicPlans ?? instance.plans)
    : [...instance.plans, ...(instance.basicPlans ?? [])];
  for (const plan of plans) {
    const lines = instantiatePlan(plan, premiseEntries);
    const result = checkChallengeProof({ premises, target: conclusion, lines });
    if (!result.ok) {
      throw new Error(
        `测试题证明计划 ${plan.id} 未通过检查：${result.error?.message ?? "未知错误"}`,
      );
    }
    const metrics = measureProofPlan(lines, policy);
    if (basicOnly && metrics.derivedRuleIds.length > 0) {
      throw new Error(`基础规则证明计划 ${plan.id} 使用了派生规则`);
    }
    const classification = classifyDifficulty(metrics, policy);
    const candidate = { planId: plan.id, lines, metrics, classification };
    if (
      !best ||
      classification.planningCost < best.classification.planningCost ||
      (classification.planningCost === best.classification.planningCost &&
        metrics.lineCount < best.metrics.lineCount)
    ) {
      best = candidate;
    }
  }
  if (!best) throw new Error("测试题没有可验证的证明计划");
  return best;
}

function citationCandidates(premiseCount, maximumArity) {
  const candidates = [""];
  const extend = (prefix, remaining) => {
    if (remaining === 0) {
      candidates.push(prefix.join(", "));
      return;
    }
    for (let number = 1; number <= premiseCount; number += 1) {
      extend([...prefix, number], remaining - 1);
    }
  };
  for (let arity = 1; arity <= maximumArity; arity += 1) {
    extend([], arity);
  }
  return candidates;
}

export function detectOneLineProof(
  { premises, conclusion },
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  const key = [
    policy.version,
    policy.generation.maxOneLineCitations,
    policy.generation.oneLineCacheSize,
    premises.join(";"),
    conclusion,
  ].join("\u0000");
  if (ONE_LINE_CACHE.has(key)) {
    const cached = ONE_LINE_CACHE.get(key);
    ONE_LINE_CACHE.delete(key);
    ONE_LINE_CACHE.set(key, cached);
    return cached;
  }

  const remember = (value) => {
    if (policy.generation.oneLineCacheSize === 0) return value;
    ONE_LINE_CACHE.set(key, value);
    while (ONE_LINE_CACHE.size > policy.generation.oneLineCacheSize) {
      ONE_LINE_CACHE.delete(ONE_LINE_CACHE.keys().next().value);
    }
    return value;
  };

  const citations = citationCandidates(
    premises.length,
    policy.generation.maxOneLineCitations,
  );
  for (const { id } of RULE_OPTIONS) {
    if (id === "assumption") continue;
    for (const citation of citations) {
      const line = {
        formula: conclusion,
        rule: id,
        citations: citation,
        path: [],
        isAssumption: false,
      };
      const result = checkChallengeProof({
        premises,
        target: conclusion,
        lines: [line],
      });
      if (result.ok) {
        const witness = Object.freeze({ rule: id, citations: citation });
        return remember(witness);
      }
    }
  }
  return remember(null);
}

function frozenDifficulty(
  plan,
  basicPlan,
  policy,
  { targetBand, attempts, fallbackUsed },
) {
  const metrics = plan.metrics;
  return Object.freeze({
    policyVersion: policy.version,
    band: plan.classification.band,
    planningCost: plan.classification.planningCost,
    trivialityScore: plan.classification.trivialityScore,
    basicOnlyPlanningCost: basicPlan.classification.planningCost,
    derivedShortcutGap: Math.max(
      0,
      basicPlan.classification.planningCost - plan.classification.planningCost,
    ),
    planId: plan.planId,
    metrics: Object.freeze({
      lineCount: metrics.lineCount,
      subproofs: metrics.subproofs,
      multiSubproofRules: metrics.multiSubproofRules,
      maxDepth: metrics.maxDepth,
      extraDepth: metrics.extraDepth,
      distinctRuleIds: Object.freeze([...metrics.distinctRuleIds]),
      extraDistinctRules: metrics.extraDistinctRules,
      derivedRuleIds: Object.freeze([...metrics.derivedRuleIds]),
    }),
    basicOnlyMetrics: Object.freeze({
      lineCount: basicPlan.metrics.lineCount,
      subproofs: basicPlan.metrics.subproofs,
      multiSubproofRules: basicPlan.metrics.multiSubproofRules,
      maxDepth: basicPlan.metrics.maxDepth,
      derivedRuleIds: Object.freeze([...basicPlan.metrics.derivedRuleIds]),
    }),
    sampling: Object.freeze({
      targetBand,
      attempts,
      fallbackUsed,
      noveltyRelaxed: false,
    }),
  });
}

function withSamplingOutcome(challenge, samplingOverrides) {
  return Object.freeze({
    ...challenge,
    difficulty: Object.freeze({
      ...challenge.difficulty,
      sampling: Object.freeze({
        ...challenge.difficulty.sampling,
        ...samplingOverrides,
      }),
    }),
  });
}

function buildCandidate(
  template,
  random,
  policy,
  { fallback = false, targetBand, attempts = 1 } = {},
) {
  const useRecognizableInstance =
    !fallback &&
    template.recognizable === true &&
    randomUnit(random) < policy.generation.recognizableTheoremChance;
  const metavariables = fallback
    ? atomicMetavariables()
    : useRecognizableInstance
      ? atomicMetavariables(random)
      : sampleMetavariables(
          random,
          policy.generation.maxMetavariableAttempts,
          policy.generation.metavariableMaxDepth[targetBand ?? "substantial"],
          { requireIndependence: template.advanced === true },
        );
  const instance = template.make(metavariables, random);
  const premiseEntries = fallback
    ? [...instance.premises]
    : shuffle(instance.premises, random);
  const premiseAsts = premiseEntries.map(({ formula }) => formula);
  if (!hasCleanSemantics(premiseAsts, instance.conclusion)) return null;

  let plan = chooseValidatedPlan(instance, premiseEntries, policy);
  let basicPlan =
    plan.metrics.derivedRuleIds.length === 0
      ? plan
      : chooseValidatedPlan(instance, premiseEntries, policy, {
          basicOnly: true,
        });
  if (plan.metrics.lineCount > 1) {
    const premiseTexts = premiseAsts.map(formatFormula);
    const conclusionText = formatFormula(instance.conclusion);
    const direct = detectOneLineProof(
      { premises: premiseTexts, conclusion: conclusionText },
      policy,
    );
    if (direct) {
      const lines = [
        {
          formula: conclusionText,
          rule: direct.rule,
          citations: direct.citations,
          path: [],
          isAssumption: false,
        },
      ];
      const metrics = measureProofPlan(lines, policy);
      plan = {
        planId: `detected-${direct.rule}`,
        lines,
        metrics,
        classification: classifyDifficulty(metrics, policy),
      };
      if (
        metrics.derivedRuleIds.length === 0 &&
        plan.classification.planningCost <
          basicPlan.classification.planningCost
      ) {
        basicPlan = plan;
      }
    }
  }
  if (targetBand && plan.classification.band !== targetBand) return null;

  const premiseTexts = Object.freeze(premiseAsts.map(formatFormula));
  const conclusionText = formatFormula(instance.conclusion);
  return Object.freeze({
    templateId: template.id,
    premises: premiseTexts,
    conclusion: conclusionText,
    difficulty: frozenDifficulty(plan, basicPlan, policy, {
      targetBand: targetBand ?? plan.classification.band,
      attempts,
      fallbackUsed: fallback,
    }),
  });
}

function templatePools(policy) {
  const cacheKey = JSON.stringify({
    score: policy.score,
    thresholds: policy.thresholds,
    maxOneLineCitations: policy.generation.maxOneLineCitations,
  });
  let pools = TEMPLATE_POOL_CACHE.get(cacheKey);
  if (!pools) {
    pools = Object.fromEntries(
      DIFFICULTY_BANDS.map((band) => [band, []]),
    );
    const probeRandom = () => 0;
    for (const template of CHALLENGE_TEMPLATES) {
      const probe = buildCandidate(template, probeRandom, policy, {
        fallback: true,
      });
      if (!probe) {
        throw new Error(`题型 ${template.id} 无法生成用于难度分层的基准实例`);
      }
      pools[probe.difficulty.band].push(template);
    }
    Object.values(pools).forEach(Object.freeze);
    Object.freeze(pools);
    TEMPLATE_POOL_CACHE.set(cacheKey, pools);
  }
  for (const band of DIFFICULTY_BANDS) {
    if (policy.bandWeights[band] > 0 && pools[band].length === 0) {
      throw new RangeError(`难度策略要求抽取 ${band}，但没有题型落在该层`);
    }
  }
  return pools;
}

export class ChallengeGenerationError extends Error {
  constructor(band, attempts) {
    super(`未能在 ${attempts} 次尝试内生成 ${band} 难度的命题测试题`);
    this.name = "ChallengeGenerationError";
    this.band = band;
    this.attempts = attempts;
  }
}

export function createPropositionalChallengeSampler({
  random = Math.random,
  policy: policyOverrides = DEFAULT_CHALLENGE_POLICY,
} = {}) {
  if (typeof random !== "function") throw new TypeError("random 必须是函数");
  const policy = createChallengePolicy(policyOverrides);
  const pools = templatePools(policy);
  for (const band of DIFFICULTY_BANDS) {
    if (policy.bandWeights[band] === 0) continue;
    const advancedCount = pools[band].filter(
      (template) => template.advanced === true,
    ).length;
    const ordinaryCount = pools[band].length - advancedCount;
    const advancedChance = policy.generation.advancedChanceByBand[band];
    if (advancedChance > 0 && advancedCount === 0) {
      throw new RangeError(`${band} 难度层没有进阶题型可供抽样`);
    }
    if (advancedChance < 1 && ordinaryCount === 0) {
      throw new RangeError(`${band} 难度层没有普通题型可供抽样`);
    }
  }
  const recentSignatures = [];
  const recentShapeSignatures = [];
  const recentTemplateIds = [];

  const challengeSignature = (challenge) =>
    `${[...challenge.premises].sort().join(";")}⊢${challenge.conclusion}`;

  const challengeShapeSignature = (challenge) => {
    // Treat p/q/r renamings as the same exercise shape.
    const signatures = ATOM_PERMUTATIONS.map((permutation) => {
      const names = Object.fromEntries(
        ATOM_NAMES.map((name, index) => [name, permutation[index]]),
      );
      const rename = (formula) =>
        formula.replace(/[pqr]/gu, (name) => names[name]);
      return `${challenge.premises.map(rename).sort().join(";")}⊢${rename(
        challenge.conclusion,
      )}`;
    });
    return signatures.sort()[0];
  };

  const remember = (challenge) => {
    if (policy.generation.recentChallengeWindow > 0) {
      recentSignatures.push(challengeSignature(challenge));
      recentSignatures.splice(
        0,
        Math.max(
          0,
          recentSignatures.length - policy.generation.recentChallengeWindow,
        ),
      );
    }
    if (policy.generation.recentShapeWindow > 0) {
      recentShapeSignatures.push(challengeShapeSignature(challenge));
      recentShapeSignatures.splice(
        0,
        Math.max(
          0,
          recentShapeSignatures.length - policy.generation.recentShapeWindow,
        ),
      );
    }
    if (policy.generation.recentTemplateWindow > 0) {
      recentTemplateIds.push(challenge.templateId);
      recentTemplateIds.splice(
        0,
        Math.max(
          0,
          recentTemplateIds.length - policy.generation.recentTemplateWindow,
        ),
      );
    }
    return challenge;
  };

  const sample = () => {
    const targetBand = selectDifficultyBand(randomUnit(random), policy);
    const pool = pools[targetBand];
    // The advanced decision happens only after the band is fixed. Every retry
    // stays in that group, so rejection and novelty checks cannot skew bands.
    const advancedPool = pool.filter((template) => template.advanced === true);
    const ordinaryPool = pool.filter((template) => template.advanced !== true);
    const wantsAdvanced =
      advancedPool.length > 0 &&
      (ordinaryPool.length === 0 ||
        randomUnit(random) < policy.generation.advancedChanceByBand[targetBand]);
    const categoryPool = wantsAdvanced ? advancedPool : ordinaryPool;
    const cooledPool = categoryPool.filter(
      (template) => !recentTemplateIds.includes(template.id),
    );
    const selectionPool = cooledPool.length > 0 ? cooledPool : categoryPool;
    let repeatedCandidate = null;
    for (
      let attempt = 1;
      attempt <= policy.generation.maxAttemptsPerBand;
      attempt += 1
    ) {
      const template = weightedTemplate(selectionPool, random);
      const challenge = buildCandidate(template, random, policy, {
        targetBand,
        attempts: attempt,
      });
      if (!challenge) continue;
      if (
        !recentSignatures.includes(challengeSignature(challenge)) &&
        !recentShapeSignatures.includes(challengeShapeSignature(challenge))
      ) {
        return remember(challenge);
      }
      repeatedCandidate ??= challenge;
    }

    const fallbackRandom = () => 0;
    const fallbackTemplates = [
      ...selectionPool,
      ...categoryPool.filter((template) => !selectionPool.includes(template)),
    ];
    for (const template of fallbackTemplates) {
      const challenge = buildCandidate(template, fallbackRandom, policy, {
        fallback: true,
        targetBand,
        attempts: policy.generation.maxAttemptsPerBand,
      });
      if (!challenge) continue;
      if (
        !recentSignatures.includes(challengeSignature(challenge)) &&
        !recentShapeSignatures.includes(challengeShapeSignature(challenge))
      ) {
        return remember(challenge);
      }
      repeatedCandidate ??= challenge;
    }
    if (repeatedCandidate) {
      return remember(
        withSamplingOutcome(repeatedCandidate, {
          attempts: policy.generation.maxAttemptsPerBand,
          fallbackUsed: true,
          noveltyRelaxed: true,
        }),
      );
    }
    throw new ChallengeGenerationError(
      targetBand,
      policy.generation.maxAttemptsPerBand,
    );
  };

  return Object.freeze({ policy, sample });
}

export function samplePropositionalChallenge(
  random = Math.random,
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  return createPropositionalChallengeSampler({ random, policy }).sample();
}
