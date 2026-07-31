import assert from "node:assert/strict";

import { RULE_OPTIONS, checkProof, parseCitations } from "../fitch/checker.mjs";

const line = (formula, rule, citations = "", path = [], isAssumption = false) => ({
  formula,
  rule,
  citations,
  path,
  isAssumption,
});

const assumption = (formula, path) => line(formula, "assumption", "", path, true);

function valid(name, premises, lines) {
  const result = checkProof({ premises, lines });
  assert.equal(result.ok, true, `${name}: ${result.error?.message ?? "proof rejected"}`);
  return result;
}

function invalid(name, premises, lines, code, lineNumber = undefined) {
  const result = checkProof({ premises, lines });
  assert.equal(result.ok, false, `${name}: invalid proof accepted`);
  assert.equal(result.error.code, code, `${name}: ${result.error.message}`);
  if (lineNumber !== undefined) assert.equal(result.error.lineNumber, lineNumber, name);
  return result.error;
}

assert.deepEqual(parseCitations("1, 2, 4-6, 8–10"), [
  { type: "line", line: 1 },
  { type: "line", line: 2 },
  { type: "range", start: 4, end: 6 },
  { type: "range", start: 8, end: 10 },
]);
assert.deepEqual(parseCitations("  "), []);
assert.equal(RULE_OPTIONS.length, 24);
assert.equal(RULE_OPTIONS.some(({ id }) => id === "not-elim"), false);
assert.equal(RULE_OPTIONS.some(({ id }) => id === "explosion"), false);
assert.equal(
  RULE_OPTIONS.find(({ id }) => id === "indirect-proof")?.label,
  "反证法",
);
assert.equal(checkProof({ premises: [], lines: [] }).error.code, "EMPTY_PROOF");

valid("assumption", [], [assumption("p", ["a"])]);
valid("reiteration and alpha equivalence", ["∀x P(x)"], [
  line("∀y P(y)", "reiteration", "1"),
]);
valid(
  "backslash commands flow through proof checking",
  [String.raw`\forall x(P(x) \implies Q(x))`, "P(a)"],
  [
    line(String.raw`P(a) \implies Q(a)`, "forall-elim", "1"),
    line("Q(a)", "implies-elim", "2, 3"),
  ],
);
valid("and intro", ["p", "q"], [line("p ∧ q", "and-intro", "2, 1")]);
valid("and elim", ["p ∧ q"], [line("q", "and-elim", "1")]);
valid("or intro", ["p"], [line("q ∨ p", "or-intro", "1")]);
valid("or elim", ["p ∨ q", "p → r", "q → r"], [
  assumption("p", ["left"]),
  line("r", "implies-elim", "2, 4", ["left"]),
  assumption("q", ["right"]),
  line("r", "implies-elim", "3, 6", ["right"]),
  line("r", "or-elim", "1, 4-5, 6–7"),
]);
valid("implies intro", [], [
  assumption("p", ["conditional"]),
  line("p", "reiteration", "1", ["conditional"]),
  line("p → p", "implies-intro", "1-2"),
]);
valid("implies elim", ["p → q", "p"], [line("q", "implies-elim", "2, 1")]);
valid("iff intro", ["p → q", "q → p"], [
  assumption("p", ["forward"]),
  line("q", "implies-elim", "1, 3", ["forward"]),
  assumption("q", ["back"]),
  line("p", "implies-elim", "2, 5", ["back"]),
  line("p ↔ q", "iff-intro", "3-4, 5-6"),
]);
valid("iff elim", ["p ↔ q", "q"], [line("p", "iff-elim", "2, 1")]);
valid("not intro", ["¬p"], [
  assumption("p", ["negation"]),
  line("p ∧ ¬p", "and-intro", "2, 1", ["negation"]),
  line("¬p", "not-intro", "2-3"),
]);
valid("not intro with reversed explicit contradiction", ["¬p"], [
  assumption("p", ["negation"]),
  line("¬p ∧ p", "and-intro", "1, 2", ["negation"]),
  line("¬p", "not-intro", "2-3"),
]);
valid("indirect proof", ["¬¬p"], [
  assumption("¬p", ["ip"]),
  line("¬p ∧ ¬¬p", "and-intro", "2, 1", ["ip"]),
  line("p", "indirect-proof", "2-3"),
]);
valid("not intro accepts alpha-equivalent contradiction conjuncts", ["¬∀x P(x)"], [
  assumption("∀y P(y)", ["negation"]),
  line("¬∀x P(x) ∧ ∀y P(y)", "and-intro", "1, 2", ["negation"]),
  line("¬∀z P(z)", "not-intro", "2-3"),
]);
valid("forall intro", ["∀x P(x)"], [
  line("P(c)", "forall-elim", "1"),
  line("∀y P(y)", "forall-intro", "2"),
]);
valid("forall elim with compound term", ["∀x P(x)"], [
  line("P(f(a))", "forall-elim", "1"),
]);
valid("exists intro", ["P(f(a))"], [line("∃x P(x)", "exists-intro", "1")]);
valid("exists elim", ["∃x P(x)", "∀x(P(x) → q)"], [
  assumption("P(c)", ["witness"]),
  line("P(c) → q", "forall-elim", "2", ["witness"]),
  line("q", "implies-elim", "3, 4", ["witness"]),
  line("q", "exists-elim", "1, 3-5"),
]);
valid("identity intro", [], [line("f(a) = f(a)", "identity-intro")]);
valid("identity elim selectively and inside a function", ["a = b", "P(f(a), a)"], [
  line("P(f(b), a)", "identity-elim", "2, 1"),
]);
valid("disjunctive syllogism", ["p ∨ q", "¬q"], [
  line("p", "disjunctive-syllogism", "2, 1"),
]);
valid("modus tollens", ["p → q", "¬q"], [line("¬p", "modus-tollens", "1, 2")]);
valid("double negation", ["¬¬p"], [line("p", "double-negation", "1")]);
valid("excluded middle", ["p → r", "¬p → r"], [
  assumption("p", ["positive"]),
  line("r", "implies-elim", "1, 3", ["positive"]),
  assumption("¬p", ["negative"]),
  line("r", "implies-elim", "2, 5", ["negative"]),
  line("r", "excluded-middle", "3-4, 5-6"),
]);
valid("demorgan", ["¬(p ∨ q)"], [line("¬p ∧ ¬q", "demorgan", "1")]);
valid("demorgan reverse", ["¬p ∨ ¬q"], [line("¬(p ∧ q)", "德摩根律", "1")]);
valid("quantifier conversion with alpha rename", ["∀x ¬P(x)"], [
  line("¬∃y P(y)", "quantifier-conversion", "1"),
]);
valid("quantifier conversion reverse", ["¬∀x P(x)"], [
  line("∃y ¬P(y)", "quantifier-conversion", "1"),
]);

invalid("not intro rejects a noncontradictory conjunction", ["¬p", "¬q"], [
  assumption("p", ["negation"]),
  line("p ∧ ¬q", "and-intro", "3, 2", ["negation"]),
  line("¬p", "not-intro", "3-4"),
], "RULE_NOT_SATISFIED", 5);
invalid("not intro rejects a contradiction nested inside a larger conjunction", ["¬p", "q"], [
  assumption("p", ["negation"]),
  line("p ∧ ¬p", "and-intro", "3, 1", ["negation"]),
  line("(p ∧ ¬p) ∧ q", "and-intro", "4, 2", ["negation"]),
  line("¬p", "not-intro", "3-5"),
], "RULE_NOT_SATISFIED", 6);
invalid("proof by contradiction requires an explicit contradiction", ["¬¬p", "q"], [
  assumption("¬p", ["ip"]),
  line("¬p ∧ q", "and-intro", "3, 2", ["ip"]),
  line("p", "indirect-proof", "3-4"),
], "RULE_NOT_SATISFIED", 5);
invalid("proof by contradiction requires the negation of its conclusion", ["¬p"], [
  assumption("p", ["ip"]),
  line("p ∧ ¬p", "and-intro", "2, 1", ["ip"]),
  line("q", "indirect-proof", "2-3"),
], "RULE_NOT_SATISFIED", 4);
invalid("removed negation elimination rule is rejected", ["p", "¬p"], [
  line("p ∧ ¬p", "not-elim", "1, 2"),
], "UNKNOWN_RULE", 3);
invalid("removed explosion rule is rejected", ["p"], [
  line("q", "explosion", "1"),
], "UNKNOWN_RULE", 2);

valid("parent formula available in nested subproof", ["p"], [
  line("p", "reiteration", "1"),
  assumption("q", ["outer"]),
  assumption("r", ["outer", "inner"]),
  line("p", "reiteration", "2", ["outer", "inner"]),
]);
valid("completed parent-level subproof available from sibling", [], [
  assumption("p", ["first"]),
  line("p", "reiteration", "1", ["first"]),
  assumption("q", ["second"]),
  line("p → p", "implies-intro", "1-2", ["second"]),
]);

invalid("closed sibling line inaccessible", [], [
  assumption("p", ["first"]),
  line("p", "reiteration", "1", ["first"]),
  assumption("q", ["second"]),
  line("p", "reiteration", "2", ["second"]),
], "INACCESSIBLE_LINE", 4);
invalid("self reference", [], [line("p", "reiteration", "1")], "FORWARD_REFERENCE", 1);
invalid("forward reference", [], [
  line("p", "reiteration", "2"),
  line("p", "reiteration", "1"),
], "FORWARD_REFERENCE", 1);
invalid("malformed range", ["p"], [line("p", "reiteration", "1--2")], "MALFORMED_CITATION", 2);
invalid("range must begin with assumption", ["p"], [
  line("p", "reiteration", "1"),
  line("p → p", "implies-intro", "2-2"),
], "INVALID_SUBPROOF", 3);
invalid("range must cite the actual final line at its own depth", [], [
  assumption("p", ["box"]),
  line("p", "reiteration", "1", ["box"]),
  line("p", "reiteration", "2", ["box"]),
  line("p → p", "implies-intro", "1-2"),
], "INVALID_SUBPROOF", 4);
valid("range may cite the actual final line at its own depth", [], [
  assumption("p", ["box"]),
  line("p", "reiteration", "1", ["box"]),
  line("p", "reiteration", "2", ["box"]),
  line("p → p", "implies-intro", "1-3"),
]);
invalid("open range cannot be discharged", [], [
  assumption("p", ["open"]),
  line("p → p", "implies-intro", "1-1", ["open"]),
], "OPEN_SUBPROOF", 2);
invalid("new scope requires assumption", ["p"], [
  line("p", "reiteration", "1", ["box"]),
], "MISSING_ASSUMPTION", 2);
invalid("assumption requires new scope", [], [assumption("p", [])], "ASSUMPTION_WITHOUT_NEW_SCOPE", 1);
invalid("cannot skip a scope level", [], [assumption("p", ["one", "two"])], "SKIPPED_SUBPROOF_LEVEL", 1);

invalid("forall intro eigenconstant in premise", ["P(c)"], [
  line("∀x P(x)", "forall-intro", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("forall intro needs bare parameter", ["∀x P(x)"], [
  line("P(f(a))", "forall-elim", "1"),
  line("∀x P(x)", "forall-intro", "2"),
], "RULE_NOT_SATISFIED", 3);
invalid("forall intro eigenconstant in open assumption", ["∀x P(x)"], [
  assumption("Q(c)", ["open"]),
  line("P(c)", "forall-elim", "1", ["open"]),
  line("∀x P(x)", "forall-intro", "3", ["open"]),
], "RULE_NOT_SATISFIED", 4);
invalid("exists elim witness in conclusion", ["∃x P(x)"], [
  assumption("P(c)", ["witness"]),
  line("P(c)", "reiteration", "2", ["witness"]),
  line("P(c)", "exists-elim", "1, 2-3"),
], "RULE_NOT_SATISFIED", 4);
invalid("exists elim witness in premise", ["∃x P(x)", "q ∨ P(c)"], [
  assumption("P(c)", ["witness"]),
  line("q ∨ P(c)", "reiteration", "2", ["witness"]),
  line("q ∨ P(c)", "exists-elim", "1, 3-4"),
], "RULE_NOT_SATISFIED", 5);

const arityError = invalid("predicate arity conflict", ["P(a)"], [
  line("P(a, b)", "reiteration", "1"),
], "INCONSISTENT_ARITY", 2);
assert.equal(arityError.kind, "signature");
assert.equal(arityError.symbolKind, "predicate");
invalid("function arity conflict", ["P(f(a))"], [
  line("P(f(a, b))", "reiteration", "1"),
], "INCONSISTENT_ARITY", 2);
invalid("capture-creating universal elimination rejected", ["∀x ∀y P(x, y)"], [
  line("∀y P(y, y)", "forall-elim", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("identity elim must replace at least once", ["a = b", "P(a)"], [
  line("P(a)", "identity-elim", "1, 2"),
], "RULE_NOT_SATISFIED", 3);
invalid("identity elim cannot capture", ["x = a", "∀x P(a)"], [
  line("∀x P(x)", "identity-elim", "1, 2"),
], "RULE_NOT_SATISFIED", 3);

const firstError = invalid("first rule error", ["p"], [
  line("q", "reiteration", "1"),
  line("p ∧ p", "and-intro", "1, 1"),
], "RULE_NOT_SATISFIED", 2);
assert.match(firstError.message, /重申/u);
invalid("earlier rule error beats later syntax error", ["p"], [
  line("q", "reiteration", "1"),
  line("P(", "reiteration", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("earlier rule error beats later citation error", ["p"], [
  line("q", "reiteration", "1"),
  line("p", "reiteration", "99"),
], "RULE_NOT_SATISFIED", 2);
invalid("earlier syntax error beats later structure error", ["p"], [
  line("P(", "reiteration", "1"),
  line("p", "reiteration", "1", ["skipped", "level"]),
], "EXPECTED_TERM", 2);

const success = valid("Chinese labels accepted", ["p"], [line("p", "重申", "1")]);
assert.equal(success.premiseCount, 1);
assert.equal(success.lineCount, 1);
assert.equal(success.conclusion.kind, "proposition");

console.log(
  `Fitch checker passed ${RULE_OPTIONS.length} rule options, scope, citation, signature, eigenvariable, alpha-equivalence, and first-error tests.`,
);
