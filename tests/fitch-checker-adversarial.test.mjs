import assert from "node:assert/strict";

import { RULE_OPTIONS, checkProof, parseCitations } from "../fitch/checker.mjs";

const line = (formula, rule, citations = "", path = [], isAssumption = false) => ({
  formula,
  rule,
  citations,
  path,
  isAssumption,
});

const assumption = (formula, path) => line(formula, "假设", "", path, true);

let assertionCount = 0;

function valid(name, premises, lines) {
  const result = checkProof({ premises, lines });
  assert.equal(result.ok, true, `${name}: ${result.error?.code ?? "rejected"}: ${result.error?.message ?? ""}`);
  assertionCount += 1;
  return result;
}

function invalid(name, premises, lines, code, lineNumber = undefined) {
  const result = checkProof({ premises, lines });
  assert.equal(result.ok, false, `${name}: invalid proof accepted`);
  assert.equal(result.error.code, code, `${name}: ${result.error.message}`);
  if (lineNumber !== undefined) assert.equal(result.error.lineNumber, lineNumber, name);
  assertionCount += 1;
  return result.error;
}

function rejected(name, premises, lines, lineNumber = undefined) {
  const result = checkProof({ premises, lines });
  assert.equal(result.ok, false, `${name}: invalid proof accepted`);
  if (lineNumber !== undefined) assert.equal(result.error.lineNumber, lineNumber, name);
  assertionCount += 1;
  return result.error;
}

// Citation input is deliberately textual: Chinese punctuation and flexible
// spacing are accepted, but ranges remain single subproof citations.
assert.deepEqual(parseCitations(" 1 ， 2–4, 5 - 7 "), [
  { type: "line", line: 1 },
  { type: "range", start: 2, end: 4 },
  { type: "range", start: 5, end: 7 },
]);
assert.throws(() => parseCitations("1,"), SyntaxError);
assert.throws(() => parseCitations({ line: 1 }), TypeError);
assert.throws(() => parseCitations("0"), SyntaxError);
assertionCount += 4;

// Exercise every advertised rule through the checker, primarily with Chinese
// labels and with alpha-renamed quantified formulas where a rule permits it.
const exercisedRules = new Set();
const exercise = (id, name, premises, lines) => {
  exercisedRules.add(id);
  return valid(name, premises, lines);
};

exercise("assumption", "assumption alias", [], [assumption("p", ["box"])]);
exercise("reiteration", "reiteration modulo alpha-renaming", ["任意 x ((P(x)))"], [
  line("∀y P(y)", "重申", "1"),
]);
exercise("and-intro", "and intro accepts Chinese connective and reversed citations", ["p", "q"], [
  line("q 且 p", "合取引入", "2，1"),
]);
exercise("and-elim", "and elim returns an alpha-equivalent conjunct", ["(∀x P(x)) ∧ q"], [
  line("任意 y P(y)", "合取消去", "1"),
]);
exercise("or-intro", "or intro returns an alpha-equivalent disjunct", ["∀x P(x)"], [
  line("q 或 任意 y P(y)", "析取引入", "1"),
]);
exercise("or-elim", "or elim with ranges in reverse branch order", ["p ∨ q", "p → r", "q → r"], [
  assumption("q", ["right"]),
  line("r", "条件消去", "3, 4", ["right"]),
  assumption("p", ["left"]),
  line("r", "条件消去", "2, 6", ["left"]),
  line("r", "析取消去", "1, 6-7, 4-5"),
]);
exercise("implies-intro", "one-line subproof can introduce a conditional", [], [
  assumption("p", ["conditional"]),
  line("p → p", "条件引入", "1-1"),
]);
exercise("implies-elim", "conditional elimination uses alpha-equivalent antecedent", [
  "(∀x P(x)) → q",
  "任意 y P(y)",
], [line("q", "条件消去", "2, 1")]);
exercise("iff-intro", "biconditional intro with reversed range citations", ["p → q", "q → p"], [
  assumption("p", ["forward"]),
  line("q", "条件消去", "1, 3", ["forward"]),
  assumption("q", ["backward"]),
  line("p", "条件消去", "2, 5", ["backward"]),
  line("p ↔ q", "双条件引入", "5-6, 3-4"),
]);
exercise("iff-elim", "biconditional elimination in reverse direction", ["p ↔ q", "q"], [
  line("p", "双条件消去", "2, 1"),
]);
exercise("not-intro", "negation intro", ["¬p"], [
  assumption("p", ["negation"]),
  line("p 且 非 p", "合取引入", "2, 1", ["negation"]),
  line("非 p", "否定引入", "2-3"),
]);
exercise("indirect-proof", "indirect proof modulo alpha-renaming", ["¬¬∀x P(x)"], [
  assumption("¬∀y P(y)", ["ip"]),
  line("(¬∀y P(y)) ∧ (¬¬∀x P(x))", "合取引入", "2, 1", ["ip"]),
  line("任意 z P(z)", "反证法", "2-3"),
]);
valid("negation intro accepts a reversed explicit contradiction", ["¬q"], [
  assumption("q", ["negation"]),
  line("¬q ∧ q", "合取引入", "1, 2", ["negation"]),
  line("¬q", "否定引入", "2-3"),
]);
valid("negation intro accepts alpha-equivalent contradiction conjuncts", ["¬∀x P(x)"], [
  assumption("∀y P(y)", ["negation"]),
  line("(∀y P(y)) ∧ (¬∀x P(x))", "合取引入", "2, 1", ["negation"]),
  line("¬∀z P(z)", "否定引入", "2-3"),
]);
valid("negation intro accepts equality as the contradicted formula", ["¬(a = b)"], [
  assumption("a = b", ["negation"]),
  line("(a = b) ∧ ¬(a = b)", "合取引入", "2, 1", ["negation"]),
  line("¬(a = b)", "否定引入", "2-3"),
]);
invalid("negation intro rejects mismatched contradiction conjuncts", ["¬p", "¬q"], [
  assumption("p", ["negation"]),
  line("p ∧ ¬q", "合取引入", "3, 2", ["negation"]),
  line("¬p", "否定引入", "3-4"),
], "RULE_NOT_SATISFIED", 5);
invalid("negation intro rejects a disjunction of opposites", ["¬p"], [
  assumption("p", ["negation"]),
  line("p ∨ ¬p", "析取引入", "2", ["negation"]),
  line("¬p", "否定引入", "2-3"),
], "RULE_NOT_SATISFIED", 4);
invalid("negation intro rejects an alpha-mismatched contradiction", ["¬∀x Q(x)"], [
  assumption("∀y P(y)", ["negation"]),
  line("(∀y P(y)) ∧ (¬∀x Q(x))", "合取引入", "2, 1", ["negation"]),
  line("¬∀z P(z)", "否定引入", "2-3"),
], "RULE_NOT_SATISFIED", 4);
exercise("forall-intro", "universal intro with subscripted eigenconstant", ["∀x_10 P(x_10)"], [
  line("P(c_10)", "全称消去", "1"),
  line("任意 y_20 P(y_20)", "全称引入", "2"),
]);
exercise("forall-elim", "universal elim avoids capture by alpha-renaming", ["∀x ∃y P(x, y)"], [
  line("存在 z P(y, z)", "全称消去", "1"),
]);
exercise("exists-intro", "existential intro avoids capture by alpha-renaming", ["∃z P(y, z)"], [
  line("存在 x 存在 z P(x, z)", "存在引入", "1"),
]);
exercise("exists-elim", "existential elim with alpha-renamed witness matrix", [
  "∃x ∀y P(x, y)",
  "∀x((∀y P(x, y)) → q)",
], [
  assumption("任意 z P(c, z)", ["witness"]),
  line("(∀z P(c, z)) → q", "全称消去", "2", ["witness"]),
  line("q", "条件消去", "3, 4", ["witness"]),
  line("q", "存在消去", "1, 3-5"),
]);
exercise("identity-intro", "identity intro on compound terms", [], [
  line("f_2(g(a), x_1) = f_2(g(a), x_1)", "等同引入"),
]);
exercise("identity-elim", "identity elim selectively replaces nested terms", [
  "a = b",
  "P(a, f(a), a)",
], [line("P(b, f(a), b)", "等同消去", "2, 1")]);
exercise("disjunctive-syllogism", "disjunctive syllogism", ["p ∨ q", "¬p"], [
  line("q", "析取三段论", "2, 1"),
]);
exercise("modus-tollens", "modus tollens modulo alpha-renaming", [
  "(∀x P(x)) → q",
  "¬q",
], [line("¬∀y P(y)", "否定后件式", "1, 2")]);
exercise("double-negation", "double-negation elimination modulo alpha-renaming", ["¬¬∀x P(x)"], [
  line("任意 y P(y)", "双重否定消去", "1"),
]);
exercise("excluded-middle", "excluded-middle proof by cases", ["p → r", "¬p → r"], [
  assumption("p", ["positive"]),
  line("r", "条件消去", "1, 3", ["positive"]),
  assumption("¬p", ["negative"]),
  line("r", "条件消去", "2, 5", ["negative"]),
  line("r", "排中律", "3-4, 5-6"),
]);
exercise("demorgan", "De Morgan rewrite with quantified alpha-renaming", ["¬((∀x P(x)) ∨ q)"], [
  line("(¬∀y P(y)) ∧ ¬q", "德摩根律", "1"),
]);
exercise("quantifier-conversion", "quantifier conversion with alpha-renaming", ["¬∃x P(x)"], [
  line("∀y ¬P(y)", "量词转换", "1"),
]);

assert.deepEqual(
  [...exercisedRules].sort(),
  RULE_OPTIONS.map(({ id }) => id).sort(),
  "the adversarial suite must cover every rule exposed by the dropdown",
);
assertionCount += 1;

// The liberal forall-x convention: a line in any ancestor proof and a
// completed subproof belonging to any ancestor proof remain citable. Closed
// sibling lines themselves, and subproofs owned by a sibling proof, do not.
valid("root and parent lines are visible at arbitrary depth", ["p"], [
  line("p", "重申", "1"),
  assumption("q", ["outer"]),
  line("q", "重申", "3", ["outer"]),
  assumption("r", ["outer", "inner"]),
  line("p ∧ q", "合取引入", "2, 4", ["outer", "inner"]),
]);

valid("completed subproof in parent proof is visible from a deeper sibling", [], [
  assumption("q", ["outer"]),
  assumption("p", ["outer", "finished"]),
  line("p", "重申", "2", ["outer", "finished"]),
  assumption("r", ["outer", "current"]),
  assumption("q", ["outer", "current", "deep"]),
  line("p → p", "条件引入", "2-3", ["outer", "current", "deep"]),
]);

invalid("closed sibling formula is inaccessible", [], [
  assumption("r", ["outer"]),
  assumption("p", ["outer", "left"]),
  line("p", "重申", "2", ["outer", "left"]),
  assumption("q", ["outer", "right"]),
  line("p", "重申", "3", ["outer", "right"]),
], "INACCESSIBLE_LINE", 5);

invalid("subproof owned by a sibling ancestor is inaccessible", [], [
  assumption("p", ["left"]),
  assumption("q", ["left", "box"]),
  line("q", "重申", "2", ["left", "box"]),
  assumption("r", ["right"]),
  line("q → q", "条件引入", "2-3", ["right"]),
], "INACCESSIBLE_SUBPROOF", 5);

invalid("an open ancestor subproof cannot be cited as completed", [], [
  assumption("p", ["outer"]),
  line("p", "重申", "1", ["outer"]),
  assumption("q", ["outer", "inner"]),
  line("p → p", "条件引入", "1-2", ["outer", "inner"]),
], "OPEN_SUBPROOF", 4);

valid("outer subproof range ends on its final own-depth line after a nested box", [], [
  assumption("p", ["outer"]),
  line("p", "重申", "1", ["outer"]),
  assumption("q", ["outer", "inner"]),
  line("q", "重申", "3", ["outer", "inner"]),
  line("p", "重申", "2", ["outer"]),
  line("p → p", "条件引入", "1-5"),
]);

// A range must name the actual completed box, rather than an arbitrary prefix
// that happens to start at its assumption and end at the same depth.
rejected("range cannot omit a later own-depth line in the same box", [], [
  assumption("p", ["box"]),
  line("p", "重申", "1", ["box"]),
  line("p ∧ p", "合取引入", "1, 2", ["box"]),
  line("p → p", "条件引入", "1-2"),
], 4);

valid("range endpoint is the final own-depth line even when a nested box trails it", [], [
  assumption("p", ["outer"]),
  line("p", "重申", "1", ["outer"]),
  assumption("q", ["outer", "inner"]),
  line("q", "重申", "3", ["outer", "inner"]),
  line("p → p", "条件引入", "1-2"),
]);

// Alpha-equivalence must preserve binding structure and free-variable names.
valid("deep shadowing alpha-renaming", ["∀x(∀x P(x) ∧ Q(x))"], [
  line("∀y(∀z P(z) ∧ Q(y))", "重申", "1"),
]);
invalid("free variables are not alpha-renamable", ["∀x P(x, y)"], [
  line("∀z P(z, x)", "重申", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("different binding structures are not alpha-equivalent", ["∀x ∃y P(x, y)"], [
  line("∀x ∃x P(x, x)", "重申", "1"),
], "RULE_NOT_SATISFIED", 2);

// Arity is global and fixed by first appearance, for both predicates and
// functions, including multiple appearances within one formula.
invalid("predicate arity conflict after first appearance", ["P(a, b)"], [
  line("P(a)", "重申", "1"),
], "INCONSISTENT_ARITY", 2);
invalid("function arity conflict after first appearance", ["P(f(a))"], [
  line("P(f(a, b))", "重申", "1"),
], "INCONSISTENT_ARITY", 2);
invalid("arity conflict inside one formula", [], [
  line("P(g(a)) ∧ P(g(a, b))", "假设", "", ["box"], true),
], "INCONSISTENT_ARITY", 1);

// Whitespace is free except between a predicate/function symbol and its
// application parenthesis. Chinese and Unicode syntax can be mixed.
valid("mixed syntax, subscripts, redundant parentheses, and whitespace", [
  " 任意   x_10 (((P_2(f_3(a_1), (x_10)) 且 (非 q_9 或 r_4)))) ",
], [
  line("∀y_20(P_2(f_3(a_1), y_20) ∧ (¬q_9 ∨ r_4))", "重申", "1"),
]);
valid("Chinese quantifiers need no separating spaces", ["存在x(P(x)且非 q)"], [
  line("∃x(P(x) ∧ ¬q)", "重申", "1"),
]);
invalid("space immediately after predicate is rejected through checker", ["P (a)"], [
  assumption("q", ["box"]),
], "APPLICATION_WHITESPACE", 1);
invalid("space immediately after function is rejected through checker", ["P(f (a))"], [
  assumption("q", ["box"]),
], "APPLICATION_WHITESPACE", 1);

// forall-x eigenconstant restrictions. Prior discharged work is harmless;
// premises and currently open assumptions remain undischarged dependencies.
valid("forall intro permits a name used only in a closed sibling", ["∀x P(x)"], [
  assumption("Q(c)", ["old"]),
  line("Q(c)", "重申", "2", ["old"]),
  line("P(c)", "全称消去", "1"),
  line("∀y P(y)", "全称引入", "4"),
]);
invalid("forall intro rejects eigenconstant in an unrelated premise", ["∀x P(x)", "Q(c)"], [
  line("P(c)", "全称消去", "1"),
  line("∀y P(y)", "全称引入", "3"),
], "RULE_NOT_SATISFIED", 4);
invalid("forall intro rejects eigenconstant in a grandparent assumption", ["∀x P(x)"], [
  assumption("Q(c)", ["outer"]),
  assumption("r", ["outer", "inner"]),
  line("P(c)", "全称消去", "1", ["outer", "inner"]),
  line("∀y P(y)", "全称引入", "4", ["outer", "inner"]),
], "RULE_NOT_SATISFIED", 5);
invalid("forall intro rejects a parameter left fixed in the result", ["∀x ∀y R(x, y)"], [
  line("∀y R(c, y)", "全称消去", "1"),
  line("R(c, c)", "全称消去", "2"),
  line("∀x R(x, c)", "全称引入", "3"),
], "RULE_NOT_SATISFIED", 4);
invalid("forall intro requires a bare constant, not a function term", ["∀x P(x)"], [
  line("P(f(a))", "全称消去", "1"),
  line("∀y P(y)", "全称引入", "2"),
], "RULE_NOT_SATISFIED", 3);

valid("exists elim permits witness name used only in a closed sibling", [
  "∃x P(x)",
  "∀x(P(x) → q)",
], [
  assumption("R(c)", ["old"]),
  line("R(c)", "重申", "3", ["old"]),
  assumption("P(c)", ["witness"]),
  line("P(c) → q", "全称消去", "2", ["witness"]),
  line("q", "条件消去", "5, 6", ["witness"]),
  line("q", "存在消去", "1, 5-7"),
]);
invalid("exists elim rejects witness in existential premise", ["∃x P(x, c)", "∀x(P(x, c) → q)"], [
  assumption("P(c, c)", ["witness"]),
  line("P(c, c) → q", "全称消去", "2", ["witness"]),
  line("q", "条件消去", "3, 4", ["witness"]),
  line("q", "存在消去", "1, 3-5"),
], "RULE_NOT_SATISFIED", 6);
invalid("exists elim rejects witness in result", ["∃x P(x)"], [
  assumption("P(c)", ["witness"]),
  line("P(c)", "重申", "2", ["witness"]),
  line("P(c)", "存在消去", "1, 2-3"),
], "RULE_NOT_SATISFIED", 4);
invalid("exists elim rejects witness in open parent assumption", ["∃x P(x)", "∀x(P(x) → q)"], [
  assumption("R(c)", ["outer"]),
  assumption("P(c)", ["outer", "witness"]),
  line("P(c) → q", "全称消去", "2", ["outer", "witness"]),
  line("q", "条件消去", "4, 5", ["outer", "witness"]),
  line("q", "存在消去", "1, 4-6", ["outer"]),
], "RULE_NOT_SATISFIED", 7);
invalid("exists elim requires a bare witness constant", ["∃x P(x)", "∀x(P(x) → q)"], [
  assumption("P(f(a))", ["witness"]),
  line("P(f(a)) → q", "全称消去", "2", ["witness"]),
  line("q", "条件消去", "3, 4", ["witness"]),
  line("q", "存在消去", "1, 3-5"),
], "RULE_NOT_SATISFIED", 6);

// Capture-avoiding substitution is required for quantifiers and equality.
invalid("universal elimination cannot capture a variable inside a function", ["∀x ∀y P(x, y)"], [
  line("∀y P(f(y), y)", "全称消去", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("existential introduction cannot use a captured instance", ["∃y P(y, y)"], [
  line("∃x ∃y P(x, y)", "存在引入", "1"),
], "RULE_NOT_SATISFIED", 2);
valid("identity elimination allows alpha-renaming and a free functional replacement", [
  "a = f(y)",
  "∀x P(a, x, a)",
], [line("∀z P(f(y), z, a)", "等同消去", "1, 2")]);
invalid("identity elimination cannot capture a variable from a replacement function", [
  "a = f(x)",
  "∀x P(a, x)",
], [line("∀x P(f(x), x)", "等同消去", "1, 2")], "RULE_NOT_SATISFIED", 3);
invalid("identity elimination cannot replace bound occurrences", ["x = a", "∀x P(x)"], [
  line("∀x P(a)", "等同消去", "1, 2"),
], "RULE_NOT_SATISFIED", 3);
invalid("identity elimination must make at least one replacement", ["a = b", "P(a)"], [
  line("P(a)", "等同消去", "1, 2"),
], "RULE_NOT_SATISFIED", 3);
invalid("identity elimination cannot make unrelated structural changes", ["a = b", "P(a) ∨ q"], [
  line("P(b) ∧ q", "等同消去", "1, 2"),
], "RULE_NOT_SATISFIED", 3);

// Malformed, self, forward, range, missing, and extra citations must all be
// rejected deterministically on the row that contains them.
invalid("malformed doubled separator", ["p", "q"], [
  line("p ∧ q", "合取引入", "1,,2"),
], "MALFORMED_CITATION", 3);
invalid("self citation with premise offset", ["p", "q"], [
  line("p", "重申", "3"),
], "FORWARD_REFERENCE", 3);
invalid("forward formula citation", ["p"], [
  line("p", "重申", "3"),
  line("p", "重申", "1"),
], "FORWARD_REFERENCE", 2);
invalid("forward range citation", [], [
  assumption("p", ["box"]),
  line("p → p", "条件引入", "1-2", ["box"]),
], "FORWARD_REFERENCE", 2);
invalid("range cannot start at a premise", ["p"], [
  line("p → p", "条件引入", "1-1"),
], "INVALID_SUBPROOF", 2);
invalid("range endpoint must be at the assumption's own depth", [], [
  assumption("p", ["outer"]),
  assumption("q", ["outer", "inner"]),
  line("p → q", "条件引入", "1-2"),
], "INVALID_SUBPROOF", 3);
invalid("missing formula citation", ["p"], [line("p", "重申")], "RULE_NOT_SATISFIED", 2);
invalid("extra formula citation", ["p"], [line("p", "重申", "1, 1")], "RULE_NOT_SATISFIED", 2);
invalid("formula citation cannot replace required subproof citation", ["p"], [
  line("p → p", "条件引入", "1"),
], "RULE_NOT_SATISFIED", 2);
invalid("extra subproof citation", [], [
  assumption("p", ["first"]),
  assumption("q", ["second"]),
  line("p → p", "条件引入", "1-1, 2-2"),
], "RULE_NOT_SATISFIED", 3);

// "First error" means the earliest numbered row, rather than the first error
// category reached by a multi-pass implementation.
invalid("earlier rule error beats later malformed citation", ["p"], [
  line("q", "重申", "1"),
  line("p", "重申", "??"),
], "RULE_NOT_SATISFIED", 2);
invalid("earlier malformed citation beats later syntax error", ["p"], [
  line("p", "重申", "??"),
  line("P (a)", "重申", "1"),
], "MALFORMED_CITATION", 2);
invalid("earlier syntax error beats later structural error", ["p"], [
  line("P (a)", "重申", "1"),
  assumption("q", []),
], "APPLICATION_WHITESPACE", 2);
invalid("earlier signature error beats later structural error", ["P(a)"], [
  line("P(a, b)", "重申", "1"),
  assumption("q", []),
], "INCONSISTENT_ARITY", 2);

console.log(`Fitch adversarial checker passed ${assertionCount} parser-integration, rule, scope, substitution, citation, and error-order checks.`);
