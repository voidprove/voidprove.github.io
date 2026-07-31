import assert from "node:assert/strict";
import {
  FormulaSyntaxError,
  alphaEquivalent,
  collectConstants,
  collectNames,
  collectSignatureEntries,
  formatFormula,
  formatTerm,
  formulaEquals,
  freeVariables,
  matchSubstitutionInstance,
  parseFormula,
  parseTerm,
  substitute,
  termEquals,
  validateSignatures,
} from "../fitch/parser.mjs";

const parse = parseFormula;

assert.deepEqual(parse("P(a)"), {
  kind: "predicate",
  name: "P",
  args: [{ kind: "constant", name: "a" }],
});
assert.deepEqual(parse("p_10"), { kind: "proposition", name: "p_10" });
assert.deepEqual(parse("f(a, g(x_10)) = h_2(c)"), {
  kind: "equality",
  left: {
    kind: "function",
    name: "f",
    args: [
      { kind: "constant", name: "a" },
      {
        kind: "function",
        name: "g",
        args: [{ kind: "variable", name: "x_10" }],
      },
    ],
  },
  right: {
    kind: "function",
    name: "h_2",
    args: [{ kind: "constant", name: "c" }],
  },
});

const unicode = parse("∀x(P(x) → ∃y(Q(f(x), y) ∧ ¬R(y)))");
const chinese = parse("任意 x (P(x) 蕴含 存在 y (Q(f(x), y) 且 非 R(y)))");
const backslashCommands = parse(
  String.raw`\forall x (P(x) \implies \exists y (Q(f(x), y) \and \not R(y)))`,
);
assert.ok(formulaEquals(unicode, chinese));
assert.ok(formulaEquals(unicode, backslashCommands));
assert.ok(
  formulaEquals(
    parse(String.raw`(((p \and q) \or \not r) \implies p) \iff q`),
    parse("(((p ∧ q) ∨ ¬r) → p) ↔ q"),
  ),
);
assert.ok(formulaEquals(parse(String.raw`\neg p`), parse("¬p")));
assert.ok(formulaEquals(parse(String.raw`\lnot p`), parse("¬p")));
assert.ok(formulaEquals(parse(String.raw`p \land q`), parse("p ∧ q")));
assert.ok(formulaEquals(parse(String.raw`p \wedge q`), parse("p ∧ q")));
assert.ok(formulaEquals(parse(String.raw`p \lor q`), parse("p ∨ q")));
assert.ok(formulaEquals(parse(String.raw`p \vee q`), parse("p ∨ q")));
assert.ok(formulaEquals(parse(String.raw`p \to q`), parse("p → q")));
assert.ok(
  formulaEquals(parse(String.raw`p \rightarrow q`), parse("p → q")),
);
assert.ok(
  formulaEquals(
    parse(String.raw`p \leftrightarrow q`),
    parse("p ↔ q"),
  ),
);
assert.ok(formulaEquals(parse(String.raw`a \neq b`), parse("a ≠ b")));
assert.ok(formulaEquals(parse(String.raw`a \ne b`), parse("a ≠ b")));
assert.ok(
  formulaEquals(
    parse(String.raw`\forall x(P(x)\or Q(x))`),
    parse("∀x(P(x) ∨ Q(x))"),
  ),
);
assert.ok(
  formulaEquals(
    parse(String.raw`p\and(q\or r)`),
    parse("p ∧ (q ∨ r)"),
  ),
);
assert.ok(
  formulaEquals(
    parse(String.raw`\forall
      x_10 P(x_10)`),
    parse("∀x_10 P(x_10)"),
  ),
);
const leftGrouped = parse("(p ∧ q) ∨ r");
const rightGrouped = parse("p ∧ (q ∨ r)");
assert.equal(formulaEquals(leftGrouped, rightGrouped), false);
assert.equal(formatFormula(leftGrouped), "(p ∧ q) ∨ r");
assert.equal(formatFormula(rightGrouped), "p ∧ (q ∨ r)");
assert.ok(formulaEquals(parse(formatFormula(leftGrouped)), leftGrouped));
assert.ok(formulaEquals(parse(formatFormula(rightGrouped)), rightGrouped));
assert.equal(
  formulaEquals(parse("¬p ∧ q"), parse("¬(p ∧ q)")),
  false,
);
assert.equal(
  formulaEquals(
    parse("∀x P(x) → Q(x)"),
    parse("∀x(P(x) → Q(x))"),
  ),
  false,
);
for (const ambiguous of [
  "p 且 q 或 r",
  "p ∧ q ∧ r",
  "p ∨ q ∨ r",
  "p ∨ q ∧ r",
  "p → q → r",
  "p ↔ q ↔ r",
  "(p ∧ q ∨ r)",
  "¬(p ∧ q ∨ r)",
  "∀x(P(x) ∧ Q(x) → R(x))",
  String.raw`p \and q \or r`,
]) {
  assert.throws(() => parse(ambiguous), {
    code: "MISSING_BINARY_PARENTHESES",
  });
}
assert.throws(
  () => parse("p ∧ q → r"),
  (error) =>
    error instanceof FormulaSyntaxError &&
    error.code === "MISSING_BINARY_PARENTHESES" &&
    error.position === 6 &&
    error.end === 7,
);
assert.ok(formulaEquals(parse("a ≠ b"), parse("¬(a = b)")));
assert.ok(formulaEquals(parse("((a)) = (b)"), parse("a = b")));
assert.ok(formulaEquals(parse("((((p))))"), parse("p")));
assert.ok(
  formulaEquals(
    parse("P( (a), f( (x), b ) )"),
    parse("P(a, f(x, b))"),
  ),
);
const rendered = formatFormula(unicode);
assert.equal(rendered, "∀x(P(x) → ∃y(Q(f(x), y) ∧ ¬R(y)))");
assert.equal(formatFormula(backslashCommands), rendered);
assert.equal(formatFormula(parse(String.raw`\not(p \or q)`)), "¬(p ∨ q)");
assert.ok(formulaEquals(parse(rendered), unicode));
assert.equal(formatTerm(parseTerm(" f(a, g(x_2)) ")), "f(a, g(x_2))");

assert.throws(
  () => parse("P (a)"),
  (error) =>
    error instanceof FormulaSyntaxError &&
    error.code === "APPLICATION_WHITESPACE" &&
    error.position === 1,
);
assert.throws(
  () => parse("P(f (a))"),
  (error) => error.code === "APPLICATION_WHITESPACE" && error.position === 3,
);
assert.throws(() => parse("∀a P(a)"), { code: "INVALID_VARIABLE" });
assert.throws(() => parse("P()"), { code: "EMPTY_ARGUMENT_LIST" });
assert.throws(() => parse("s"), { code: "INVALID_IDENTIFIER" });
assert.throws(() => parse("x"), { code: "EXPECTED_EQUALITY" });
assert.throws(() => parse("P(a"), { code: "UNMATCHED_PARENTHESIS" });
assert.throws(() => parse(""), { code: "EMPTY_FORMULA" });
assert.throws(() => parse("⊥"), { code: "UNKNOWN_CHARACTER" });
assert.throws(() => parse("矛盾"), { code: "UNKNOWN_CHARACTER" });
assert.throws(() => parse("p ∧ ⊥"), { code: "UNKNOWN_CHARACTER" });
assert.throws(() => parse("矛盾 ∨ p"), { code: "UNKNOWN_CHARACTER" });
assert.throws(
  () => parse("😀"),
  (error) =>
    error instanceof FormulaSyntaxError &&
    error.code === "UNKNOWN_CHARACTER" &&
    error.message.includes("😀") &&
    error.position === 0 &&
    error.end === 2,
);
assert.throws(
  () => parse(String.raw`\forallx P(x)`),
  (error) =>
    error instanceof FormulaSyntaxError &&
    error.code === "UNKNOWN_COMMAND" &&
    error.position === 0 &&
    error.end === String.raw`\forallx`.length,
);
assert.throws(() => parse(String.raw`\Forall x P(x)`), {
  code: "UNKNOWN_COMMAND",
});
assert.throws(
  () => parse(String.raw`p \andq`),
  (error) =>
    error instanceof FormulaSyntaxError &&
    error.code === "UNKNOWN_COMMAND" &&
    error.position === 2 &&
    error.end === 7,
);
assert.throws(() => parse(String.raw`p \xor q`), {
  code: "UNKNOWN_COMMAND",
});
assert.throws(() => parse(String.raw`\bot`), { code: "UNKNOWN_COMMAND" });
assert.throws(() => parse(String.raw`\forall{x} P(x)`), {
  code: "UNKNOWN_CHARACTER",
});
assert.throws(() => parse(String.raw`p \and`), {
  code: "EXPECTED_FORMULA",
});
assert.throws(() => parse(String.raw`\constructor p`), {
  code: "UNKNOWN_COMMAND",
});
assert.throws(() => parse(String.raw`\toString p`), {
  code: "UNKNOWN_COMMAND",
});
assert.throws(() => parse("\\"), { code: "UNKNOWN_COMMAND" });

const redundantParentheses = `${"(".repeat(64)}p${")".repeat(64)}`;
assert.ok(formulaEquals(parse(redundantParentheses), parse("p")));
const excessiveFormulaNesting = `${"(".repeat(300)}p${")".repeat(300)}`;
assert.throws(() => parse(excessiveFormulaNesting), {
  code: "NESTING_TOO_DEEP",
});
assert.throws(() => parse(`${"¬".repeat(300)}p`), {
  code: "NESTING_TOO_DEEP",
});
const excessiveTermNesting = `${"(".repeat(300)}a${")".repeat(300)}`;
assert.throws(() => parseTerm(excessiveTermNesting), {
  code: "NESTING_TOO_DEEP",
});
const excessiveFunctionNesting = `${"f(".repeat(300)}a${")".repeat(300)}`;
assert.throws(() => parseTerm(excessiveFunctionNesting), {
  code: "NESTING_TOO_DEEP",
});
assert.throws(() => parse(`P(${excessiveFunctionNesting})`), {
  code: "NESTING_TOO_DEEP",
});

const alphaLeft = parse("∀x(P(x) → ∃x Q(x, y))");
const alphaRight = parse("∀z(P(z) → ∃z Q(z, y))");
assert.ok(alphaEquivalent(alphaLeft, alphaRight));
assert.equal(alphaEquivalent(alphaLeft, parse("∀z(P(z) → ∃z Q(z, x))")), false);
assert.equal(formulaEquals(alphaLeft, alphaRight), false);

assert.deepEqual([...freeVariables(alphaLeft)], ["y"]);
assert.deepEqual(
  [...collectConstants(parse("P(a, f(b, x)) ∧ c = g(a)"))],
  ["a", "b", "c"],
);
const names = collectNames(parse("∀x(P(a, f(x)) ∧ p)"));
assert.deepEqual([...names.variables], ["x"]);
assert.deepEqual([...names.constants], ["a"]);
assert.deepEqual([...names.functions], ["f"]);
assert.deepEqual([...names.predicates], ["P"]);
assert.deepEqual([...names.propositions], ["p"]);

const captureSource = parse("∀y P(x, y)");
const captureAvoided = substitute(captureSource, "x", parseTerm("y"));
assert.ok(alphaEquivalent(captureAvoided, parse("∀z P(y, z)")));
assert.deepEqual([...freeVariables(captureAvoided)], ["y"]);
assert.ok(
  formulaEquals(
    substitute(parse("P(x, f(x))"), "x", parseTerm("g(a)")),
    parse("P(g(a), f(g(a)))"),
  ),
);

const instanceBody = parse("P(x) → ∃y Q(f(x), y)");
const goodInstance = parse("P(g(a)) → ∃z Q(f(g(a)), z)");
const instanceMatch = matchSubstitutionInstance(instanceBody, "x", goodInstance);
assert.equal(instanceMatch.matches, true);
assert.ok(termEquals(instanceMatch.term, parseTerm("g(a)")));
assert.equal(
  matchSubstitutionInstance(
    instanceBody,
    "x",
    parse("P(g(a)) → ∃z Q(f(b), z)"),
  ).matches,
  false,
);
assert.deepEqual(matchSubstitutionInstance(parse("P(a)"), "x", parse("P(a)")), {
  matches: true,
  term: null,
});

assert.deepEqual(collectSignatureEntries(parse("P(f(a), x) ∧ p")), [
  { kind: "predicate", name: "P", arity: 2 },
  { kind: "function", name: "f", arity: 1 },
  { kind: "predicate", name: "p", arity: 0 },
]);
const consistentSignature = validateSignatures([
  parse("P(a)"),
  parse("P(f(b)) ∧ Q(a, b)"),
]);
assert.equal(consistentSignature.valid, true);
assert.equal(consistentSignature.predicates.get("P"), 1);
assert.equal(consistentSignature.functions.get("f"), 1);

const inconsistentSignature = validateSignatures([
  parse("P(a) ∧ Q(a)"),
  parse("P(a, b) ∨ Q(f(a))"),
  parse("R(g(a)) ∧ R(g(a, b))"),
]);
assert.equal(inconsistentSignature.valid, false);
assert.deepEqual(
  inconsistentSignature.warnings.map(
    ({ formulaIndex, kind, name, expectedArity, actualArity }) => ({
      formulaIndex,
      kind,
      name,
      expectedArity,
      actualArity,
    }),
  ),
  [
    {
      formulaIndex: 1,
      kind: "predicate",
      name: "P",
      expectedArity: 1,
      actualArity: 2,
    },
    {
      formulaIndex: 2,
      kind: "function",
      name: "g",
      expectedArity: 1,
      actualArity: 2,
    },
  ],
);

console.log("Fitch formula parser tests passed.");
