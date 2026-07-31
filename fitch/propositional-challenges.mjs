import {
  DEFAULT_CHALLENGE_POLICY,
  DIFFICULTY_BANDS,
  classifyDifficulty,
  createChallengePolicy,
  measureProofPlan,
  selectDifficultyBand,
} from "./challenge-difficulty.mjs?v=review6";
import { checkChallengeProof } from "./challenge-checker.mjs?v=review6";
import { RULE_OPTIONS } from "./checker.mjs?v=review6";
import { formatFormula } from "./parser.mjs?v=review6";

const ATOM_NAMES = Object.freeze(["p", "q", "r"]);
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
]);

export const PROPOSITIONAL_CHALLENGE_TEMPLATE_IDS = Object.freeze(
  CHALLENGE_TEMPLATES.map(({ id }) => id),
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

function weightedTemplate(templates, random) {
  const totalWeight = templates.reduce(
    (sum, template) => sum + (template.weight ?? 1),
    0,
  );
  let cursor = randomUnit(random) * totalWeight;
  for (const template of templates) {
    cursor -= template.weight ?? 1;
    if (cursor < 0) return template;
  }
  return templates.at(-1);
}

function decoratedFormula(name, otherName, random) {
  const atom = proposition(name);
  const roll = randomUnit(random);
  if (roll < 0.66) return atom;
  if (roll < 0.82) return negate(atom);
  return binary(
    pick(BINARY_OPERATORS, random),
    atom,
    proposition(otherName),
  );
}

function atomicMetavariables() {
  return {
    A: proposition("p"),
    B: proposition("q"),
    C: proposition("r"),
  };
}

function sampleMetavariables(random, maxAttempts) {
  for (let attempt = 0; attempt < maxAttempts; attempt += 1) {
    const names = shuffle(ATOM_NAMES, random);
    const formulas = names.map((name, index) =>
      decoratedFormula(name, names[(index + 1) % names.length], random),
    );
    if (new Set(formulas.map(formatFormula)).size === formulas.length) {
      return { A: formulas[0], B: formulas[1], C: formulas[2] };
    }
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

function semanticallyEquivalent(left, right, valuations) {
  return valuations.every(
    (valuation) =>
      evaluatePropositionalFormula(left, valuation) ===
      evaluatePropositionalFormula(right, valuation),
  );
}

function hasCleanSemantics(premises, conclusion) {
  if (!isSatisfiablePropositionalSet(premises)) return false;
  if (!isValidPropositionalArgument(premises, conclusion)) return false;
  if (premises.some((formula) => sameFormula(formula, conclusion))) return false;

  const valuations = valuationsFor([...premises, conclusion]);
  for (let first = 0; first < premises.length; first += 1) {
    for (let second = first + 1; second < premises.length; second += 1) {
      if (semanticallyEquivalent(premises[first], premises[second], valuations)) {
        return false;
      }
    }
  }
  if (premises.length > 0) {
    if (isValidPropositionalArgument([], conclusion)) return false;
    for (let index = 0; index < premises.length; index += 1) {
      const withoutCurrent = premises.filter(
        (_formula, premiseIndex) => premiseIndex !== index,
      );
      if (isValidPropositionalArgument(withoutCurrent, conclusion)) return false;
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
    premises.join(";"),
    conclusion,
  ].join("\u0000");
  if (ONE_LINE_CACHE.has(key)) return ONE_LINE_CACHE.get(key);

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
        ONE_LINE_CACHE.set(key, witness);
        return witness;
      }
    }
  }
  ONE_LINE_CACHE.set(key, null);
  return null;
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
    sampling: Object.freeze({ targetBand, attempts, fallbackUsed }),
  });
}

function buildCandidate(
  template,
  random,
  policy,
  { fallback = false, targetBand, attempts = 1 } = {},
) {
  const metavariables = fallback
    ? atomicMetavariables()
    : sampleMetavariables(random, policy.generation.maxMetavariableAttempts);
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

  const sample = () => {
    const targetBand = selectDifficultyBand(randomUnit(random), policy);
    const pool = pools[targetBand];
    for (
      let attempt = 1;
      attempt <= policy.generation.maxAttemptsPerBand;
      attempt += 1
    ) {
      const template = weightedTemplate(pool, random);
      const challenge = buildCandidate(template, random, policy, {
        targetBand,
        attempts: attempt,
      });
      if (challenge) return challenge;
    }

    const fallbackRandom = () => 0;
    for (const template of pool) {
      const challenge = buildCandidate(template, fallbackRandom, policy, {
        fallback: true,
        targetBand,
        attempts: policy.generation.maxAttemptsPerBand,
      });
      if (challenge) return challenge;
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
