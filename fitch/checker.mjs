import {
  alphaEquivalent,
  collectConstants,
  matchSubstitutionInstance,
  parseFormula,
  termEquals,
  validateSignatures,
} from "./parser.mjs?v=random7";

const option = (id, label, kind, hint) => Object.freeze({ id, label, kind, hint });

export const RULE_OPTIONS = Object.freeze([
  option("assumption", "假设", "assumption", "不引用行"),
  option("reiteration", "重申", "basic", "引用一行"),
  option("and-intro", "合取引入", "basic", "引用两行"),
  option("and-elim", "合取消去", "basic", "引用一行"),
  option("or-intro", "析取引入", "basic", "引用一行"),
  option("or-elim", "析取消去", "basic", "引用一行和两个子证明"),
  option("implies-intro", "条件引入", "basic", "引用一个子证明"),
  option("implies-elim", "条件消去", "basic", "引用两行"),
  option("iff-intro", "双条件引入", "basic", "引用两个子证明"),
  option("iff-elim", "双条件消去", "basic", "引用两行"),
  option("not-intro", "否定引入", "basic", "引用一个子证明"),
  option("indirect-proof", "反证法", "basic", "引用一个子证明"),
  option("forall-intro", "全称引入", "basic", "引用一行"),
  option("forall-elim", "全称消去", "basic", "引用一行"),
  option("exists-intro", "存在引入", "basic", "引用一行"),
  option("exists-elim", "存在消去", "basic", "引用一行和一个子证明"),
  option("identity-intro", "等同引入", "basic", "不引用行"),
  option("identity-elim", "等同消去", "basic", "引用两行"),
  option("disjunctive-syllogism", "析取三段论", "derived", "引用两行"),
  option("modus-tollens", "否定后件式", "derived", "引用两行"),
  option("double-negation", "双重否定消去", "derived", "引用一行"),
  option("excluded-middle", "排中律", "derived", "引用两个子证明"),
  option("demorgan", "德摩根律", "derived", "引用一行"),
  option("quantifier-conversion", "量词转换", "derived", "引用一行"),
]);

// Kept as a convenient short alias for clients that do not need the longer name.
export const RULES = RULE_OPTIONS;

const RULE_BY_ID = new Map(RULE_OPTIONS.map((entry) => [entry.id, entry]));
const RULE_ALIASES = new Map();

function addAliases(id, ...aliases) {
  [id, RULE_BY_ID.get(id)?.label, ...aliases].forEach((alias) => {
    if (alias) RULE_ALIASES.set(String(alias).trim(), id);
  });
}

addAliases("assumption", "AS", "假定");
addAliases("reiteration", "R");
addAliases("and-intro", "∧I", "&I");
addAliases("and-elim", "∧E", "&E");
addAliases("or-intro", "∨I");
addAliases("or-elim", "∨E");
addAliases("implies-intro", "→I");
addAliases("implies-elim", "→E");
addAliases("iff-intro", "↔I");
addAliases("iff-elim", "↔E");
addAliases("not-intro", "¬I");
addAliases("indirect-proof", "IP");
addAliases("forall-intro", "∀I");
addAliases("forall-elim", "∀E");
addAliases("exists-intro", "∃I");
addAliases("exists-elim", "∃E");
addAliases("identity-intro", "=I");
addAliases("identity-elim", "=E");
addAliases("disjunctive-syllogism", "DS");
addAliases("modus-tollens", "MT");
addAliases("double-negation", "DNE");
addAliases("excluded-middle", "LEM");
addAliases("demorgan", "DeM");
addAliases("quantifier-conversion", "CQ", "QN");

export function normalizeRuleId(rule, isAssumption = false) {
  const supplied = String(rule ?? "").trim();
  if (!supplied && isAssumption) return "assumption";
  return RULE_ALIASES.get(supplied) ?? null;
}

function normalizeRule(line) {
  return normalizeRuleId(line?.rule, line?.isAssumption === true);
}

function error(kind, code, message, record = null, extra = {}) {
  const result = { kind, code, message, ...extra };
  if (record?.type === "line") {
    result.lineNumber = record.number;
    result.proofLineIndex = record.index;
  } else if (record?.type === "premise") {
    result.premiseNumber = record.index + 1;
    result.lineNumber = record.number;
  }
  return result;
}

function failure(problem) {
  return { ok: false, error: problem };
}

function pathKey(path) {
  return JSON.stringify(path);
}

function normalizePath(value) {
  if (!Array.isArray(value)) return null;
  const path = [];
  for (const component of value) {
    if (
      !(
        (typeof component === "string" && component.trim() !== "") ||
        (typeof component === "number" && Number.isSafeInteger(component))
      )
    ) {
      return null;
    }
    path.push(String(component));
  }
  return path;
}

function commonPrefixLength(left, right) {
  let length = 0;
  while (length < left.length && length < right.length && left[length] === right[length]) {
    length += 1;
  }
  return length;
}

function isPrefix(prefix, path) {
  return prefix.length <= path.length && prefix.every((item, index) => item === path[index]);
}

/**
 * Parse a citation field such as "1, 2, 4-6". A range denotes one subproof,
 * never all of the individual lines in the interval.
 */
export function parseCitations(raw) {
  if (raw == null || String(raw).trim() === "") return [];
  if (typeof raw !== "string" && typeof raw !== "number") {
    throw new TypeError("引用须写成行号或子证明范围，例如 1, 2-4");
  }
  const source = String(raw).trim().replaceAll("，", ",");
  const pieces = source.split(",");
  if (pieces.some((piece) => piece.trim() === "")) {
    throw new SyntaxError("引用格式有误；请用逗号分隔行号或子证明范围");
  }
  return pieces.map((piece) => {
    const match = piece.trim().match(/^(\d+)(?:\s*[-–]\s*(\d+))?$/u);
    if (!match) {
      throw new SyntaxError(`无法识别引用“${piece.trim()}”`);
    }
    const start = Number(match[1]);
    const end = match[2] == null ? null : Number(match[2]);
    if (!Number.isSafeInteger(start) || start < 1 || (end != null && (!Number.isSafeInteger(end) || end < 1))) {
      throw new SyntaxError("行号必须是从 1 开始的整数");
    }
    if (end == null) return { type: "line", line: start };
    if (end < start) throw new SyntaxError("子证明范围的终止行不能早于起始行");
    return { type: "range", start, end };
  });
}

function formulasMatch(left, right) {
  return alphaEquivalent(left, right);
}

function isBinary(formula, operator) {
  return formula?.kind === "binary" && formula.operator === operator;
}

function isNegationOf(negation, formula) {
  return negation?.kind === "not" && formulasMatch(negation.value, formula);
}

function isExplicitContradiction(formula) {
  return (
    isBinary(formula, "and") &&
    (isNegationOf(formula.left, formula.right) ||
      isNegationOf(formula.right, formula.left))
  );
}

function citedFormulaRecords(record) {
  return record.references.filter((reference) => reference.type === "line").map((reference) => reference.record);
}

function citedRanges(record) {
  return record.references.filter((reference) => reference.type === "range");
}

function citationShape(record, formulaCount, rangeCount) {
  return citedFormulaRecords(record).length === formulaCount && citedRanges(record).length === rangeCount;
}

function ruleFailure(record, message) {
  return error("rule", "RULE_NOT_SATISFIED", `${RULE_BY_ID.get(record.rule)?.label ?? "规则"}：${message}`, record);
}

function openAssumptionRecords(record, allProofRecords, openerByPath) {
  const assumptions = [];
  for (let depth = 1; depth <= record.path.length; depth += 1) {
    const openerNumber = openerByPath.get(pathKey(record.path.slice(0, depth)));
    const opener = allProofRecords.find((candidate) => candidate.number === openerNumber);
    if (opener) assumptions.push(opener);
  }
  return assumptions;
}

function constantAppears(formulas, constantName) {
  return formulas.some((formula) => collectConstants(formula).has(constantName));
}

function termVariables(term, target = new Set()) {
  if (term.kind === "variable") target.add(term.name);
  if (term.kind === "function") term.args.forEach((argument) => termVariables(argument, target));
  return target;
}

function alphaTermMapped(left, right, environment) {
  if (!left || !right || left.kind !== right.kind) return false;
  if (left.kind === "variable") {
    for (let index = environment.length - 1; index >= 0; index -= 1) {
      const pair = environment[index];
      if (pair.left === left.name || pair.right === right.name) {
        return pair.left === left.name && pair.right === right.name;
      }
    }
    return left.name === right.name;
  }
  if (left.kind === "constant") return left.name === right.name;
  return (
    left.name === right.name &&
    left.args.length === right.args.length &&
    left.args.every((argument, index) => alphaTermMapped(argument, right.args[index], environment))
  );
}

function combineCounts(left, right) {
  const result = new Set();
  left.forEach((a) => right.forEach((b) => result.add(a + b)));
  return result;
}

// Check that target results from replacing one or more free occurrences of
// `from` by `to`. The dynamic comparison avoids constructing 2^n candidates.
function selectiveTermCounts(source, target, from, to, environment, sourceBound, targetBound) {
  const counts = new Set();
  if (alphaTermMapped(source, target, environment)) counts.add(0);

  const fromVariables = termVariables(from);
  const toVariables = termVariables(to);
  const sourceOccurrenceIsFree = [...fromVariables].every((name) => !sourceBound.has(name));
  const replacementAvoidsCapture = [...toVariables].every((name) => !targetBound.has(name));
  if (
    sourceOccurrenceIsFree &&
    replacementAvoidsCapture &&
    termEquals(source, from) &&
    termEquals(target, to)
  ) {
    counts.add(1);
  }

  if (
    source.kind === "function" &&
    target.kind === "function" &&
    source.name === target.name &&
    source.args.length === target.args.length
  ) {
    let nested = new Set([0]);
    source.args.forEach((argument, index) => {
      nested = combineCounts(
        nested,
        selectiveTermCounts(
          argument,
          target.args[index],
          from,
          to,
          environment,
          sourceBound,
          targetBound,
        ),
      );
    });
    nested.forEach((count) => counts.add(count));
  }
  return counts;
}

function selectiveFormulaCounts(source, target, from, to, environment = [], sourceBound = new Set(), targetBound = new Set()) {
  if (!source || !target || source.kind !== target.kind) return new Set();
  switch (source.kind) {
    case "proposition":
      return new Set(source.name === target.name ? [0] : []);
    case "predicate": {
      if (source.name !== target.name || source.args.length !== target.args.length) return new Set();
      let result = new Set([0]);
      source.args.forEach((argument, index) => {
        result = combineCounts(
          result,
          selectiveTermCounts(argument, target.args[index], from, to, environment, sourceBound, targetBound),
        );
      });
      return result;
    }
    case "equality":
      return combineCounts(
        selectiveTermCounts(source.left, target.left, from, to, environment, sourceBound, targetBound),
        selectiveTermCounts(source.right, target.right, from, to, environment, sourceBound, targetBound),
      );
    case "not":
      return selectiveFormulaCounts(source.value, target.value, from, to, environment, sourceBound, targetBound);
    case "binary":
      if (source.operator !== target.operator) return new Set();
      return combineCounts(
        selectiveFormulaCounts(source.left, target.left, from, to, environment, sourceBound, targetBound),
        selectiveFormulaCounts(source.right, target.right, from, to, environment, sourceBound, targetBound),
      );
    case "quantifier": {
      if (source.quantifier !== target.quantifier) return new Set();
      return selectiveFormulaCounts(
        source.body,
        target.body,
        from,
        to,
        [...environment, { left: source.variable, right: target.variable }],
        new Set([...sourceBound, source.variable]),
        new Set([...targetBound, target.variable]),
      );
    }
    default:
      return new Set();
  }
}

function isSelectiveReplacement(source, result, from, to) {
  return [...selectiveFormulaCounts(source, result, from, to)].some((count) => count > 0);
}

const not = (value) => ({ kind: "not", value });
const binary = (operator, left, right) => ({ kind: "binary", operator, left, right });
const quantified = (quantifier, variable, body) => ({ kind: "quantifier", quantifier, variable, body });

function isDeMorganRewrite(source, result) {
  const candidates = [];
  if (source.kind === "not" && isBinary(source.value, "or")) {
    candidates.push(binary("and", not(source.value.left), not(source.value.right)));
  }
  if (source.kind === "not" && isBinary(source.value, "and")) {
    candidates.push(binary("or", not(source.value.left), not(source.value.right)));
  }
  if (isBinary(source, "and") && source.left.kind === "not" && source.right.kind === "not") {
    candidates.push(not(binary("or", source.left.value, source.right.value)));
  }
  if (isBinary(source, "or") && source.left.kind === "not" && source.right.kind === "not") {
    candidates.push(not(binary("and", source.left.value, source.right.value)));
  }
  return candidates.some((candidate) => formulasMatch(candidate, result));
}

function isQuantifierConversion(source, result) {
  const candidates = [];
  if (source.kind === "quantifier" && source.body.kind === "not") {
    const dual = source.quantifier === "forall" ? "exists" : "forall";
    candidates.push(not(quantified(dual, source.variable, source.body.value)));
  }
  if (source.kind === "not" && source.value.kind === "quantifier") {
    const inner = source.value;
    const dual = inner.quantifier === "forall" ? "exists" : "forall";
    candidates.push(quantified(dual, inner.variable, not(inner.body)));
  }
  return candidates.some((candidate) => formulasMatch(candidate, result));
}

function checkRule(record, premises, allProofRecords, openerByPath) {
  const formulas = citedFormulaRecords(record);
  const ranges = citedRanges(record);
  const result = record.ast;
  const formulaAsts = formulas.map((entry) => entry.ast);

  switch (record.rule) {
    case "assumption":
      return citationShape(record, 0, 0) ? null : ruleFailure(record, "假设不能引用其他行");

    case "reiteration":
      return citationShape(record, 1, 0) && formulasMatch(formulaAsts[0], result)
        ? null
        : ruleFailure(record, "结论须与所引用的公式相同");

    case "and-intro": {
      const valid =
        citationShape(record, 2, 0) &&
        isBinary(result, "and") &&
        ((formulasMatch(formulaAsts[0], result.left) && formulasMatch(formulaAsts[1], result.right)) ||
          (formulasMatch(formulaAsts[1], result.left) && formulasMatch(formulaAsts[0], result.right)));
      return valid ? null : ruleFailure(record, "须引用两个合取支，并得到它们的合取");
    }

    case "and-elim": {
      const source = formulaAsts[0];
      const valid =
        citationShape(record, 1, 0) &&
        isBinary(source, "and") &&
        (formulasMatch(source.left, result) || formulasMatch(source.right, result));
      return valid ? null : ruleFailure(record, "结论须为所引用合取式的一个合取支");
    }

    case "or-intro": {
      const valid =
        citationShape(record, 1, 0) &&
        isBinary(result, "or") &&
        (formulasMatch(formulaAsts[0], result.left) || formulasMatch(formulaAsts[0], result.right));
      return valid ? null : ruleFailure(record, "所引用的公式须为结论的一个析取支");
    }

    case "or-elim": {
      if (!citationShape(record, 1, 2) || !isBinary(formulaAsts[0], "or")) {
        return ruleFailure(record, "须引用一个析取式和两个子证明");
      }
      const disjunction = formulaAsts[0];
      const [first, second] = ranges;
      const direct =
        formulasMatch(first.startRecord.ast, disjunction.left) &&
        formulasMatch(second.startRecord.ast, disjunction.right);
      const reverse =
        formulasMatch(second.startRecord.ast, disjunction.left) &&
        formulasMatch(first.startRecord.ast, disjunction.right);
      const sameConclusion = formulasMatch(first.endRecord.ast, result) && formulasMatch(second.endRecord.ast, result);
      return (direct || reverse) && sameConclusion
        ? null
        : ruleFailure(record, "两个子证明须分别假设两个析取支，并各自得到当前结论");
    }

    case "implies-intro": {
      const range = ranges[0];
      const valid =
        citationShape(record, 0, 1) &&
        isBinary(result, "implies") &&
        formulasMatch(range.startRecord.ast, result.left) &&
        formulasMatch(range.endRecord.ast, result.right);
      return valid ? null : ruleFailure(record, "条件式的前件和后件须分别是所引子证明的假设和结论");
    }

    case "implies-elim": {
      if (!citationShape(record, 2, 0)) return ruleFailure(record, "须引用一个条件式及其前件");
      const valid = formulaAsts.some((candidate, index) => {
        const other = formulaAsts[1 - index];
        return isBinary(candidate, "implies") && formulasMatch(candidate.left, other) && formulasMatch(candidate.right, result);
      });
      return valid ? null : ruleFailure(record, "引用的公式不构成有效的条件消去");
    }

    case "iff-intro": {
      if (!citationShape(record, 0, 2) || !isBinary(result, "iff")) {
        return ruleFailure(record, "须引用两个方向相反的子证明");
      }
      const [first, second] = ranges;
      const forward =
        formulasMatch(first.startRecord.ast, result.left) &&
        formulasMatch(first.endRecord.ast, result.right) &&
        formulasMatch(second.startRecord.ast, result.right) &&
        formulasMatch(second.endRecord.ast, result.left);
      const reverse =
        formulasMatch(second.startRecord.ast, result.left) &&
        formulasMatch(second.endRecord.ast, result.right) &&
        formulasMatch(first.startRecord.ast, result.right) &&
        formulasMatch(first.endRecord.ast, result.left);
      return forward || reverse ? null : ruleFailure(record, "两个子证明须分别证明两个方向");
    }

    case "iff-elim": {
      if (!citationShape(record, 2, 0)) return ruleFailure(record, "须引用一个双条件式及其一侧");
      const valid = formulaAsts.some((candidate, index) => {
        if (!isBinary(candidate, "iff")) return false;
        const side = formulaAsts[1 - index];
        return (
          (formulasMatch(side, candidate.left) && formulasMatch(result, candidate.right)) ||
          (formulasMatch(side, candidate.right) && formulasMatch(result, candidate.left))
        );
      });
      return valid ? null : ruleFailure(record, "须从双条件式的一侧推出另一侧");
    }

    case "not-intro": {
      const range = ranges[0];
      const valid =
        citationShape(record, 0, 1) &&
        result.kind === "not" &&
        formulasMatch(range.startRecord.ast, result.value) &&
        isExplicitContradiction(range.endRecord.ast);
      return valid
        ? null
        : ruleFailure(
            record,
            "子证明须以当前否定式的内部公式为假设，并以形如 φ ∧ ¬φ 的公式结束",
          );
    }

    case "indirect-proof": {
      const range = ranges[0];
      const valid =
        citationShape(record, 0, 1) &&
        isNegationOf(range.startRecord.ast, result) &&
        isExplicitContradiction(range.endRecord.ast);
      return valid
        ? null
        : ruleFailure(
            record,
            "子证明须以当前结论的否定为假设，并以形如 φ ∧ ¬φ 的公式结束",
          );
    }

    case "forall-intro": {
      if (!citationShape(record, 1, 0) || result.kind !== "quantifier" || result.quantifier !== "forall") {
        return ruleFailure(record, "结论须为全称量化式，并引用它的一个参数实例");
      }
      const match = matchSubstitutionInstance(result.body, result.variable, formulaAsts[0]);
      if (!match.matches) return ruleFailure(record, "所引用的公式不是结论矩阵的统一实例");
      if (match.term == null) return null;
      if (match.term.kind !== "constant") return ruleFailure(record, "全称引入所用的参数必须是一个常项");
      const name = match.term.name;
      if (collectConstants(result.body).has(name)) {
        return ruleFailure(record, `参数 ${name} 并未在全称化时全部被替换`);
      }
      const openAssumptions = openAssumptionRecords(record, allProofRecords, openerByPath).map((entry) => entry.ast);
      if (constantAppears([...premises.map((entry) => entry.ast), ...openAssumptions], name)) {
        return ruleFailure(record, `参数 ${name} 出现在前提或尚未解除的假设中`);
      }
      return null;
    }

    case "forall-elim": {
      const source = formulaAsts[0];
      const valid =
        citationShape(record, 1, 0) &&
        source.kind === "quantifier" &&
        source.quantifier === "forall" &&
        matchSubstitutionInstance(source.body, source.variable, result).matches;
      return valid ? null : ruleFailure(record, "结论须为所引用全称式的一个代入实例");
    }

    case "exists-intro": {
      const valid =
        citationShape(record, 1, 0) &&
        result.kind === "quantifier" &&
        result.quantifier === "exists" &&
        matchSubstitutionInstance(result.body, result.variable, formulaAsts[0]).matches;
      return valid ? null : ruleFailure(record, "所引用的公式须为存在量化式矩阵的一个代入实例");
    }

    case "exists-elim": {
      if (!citationShape(record, 1, 1)) return ruleFailure(record, "须引用一个存在量化式和一个子证明");
      const source = formulaAsts[0];
      const range = ranges[0];
      if (source.kind !== "quantifier" || source.quantifier !== "exists") {
        return ruleFailure(record, "所引用的公式须为存在量化式");
      }
      const match = matchSubstitutionInstance(source.body, source.variable, range.startRecord.ast);
      if (!match.matches || !formulasMatch(range.endRecord.ast, result)) {
        return ruleFailure(record, "子证明须以存在式的见证实例为假设，并得到当前结论");
      }
      if (match.term == null) return null;
      if (match.term.kind !== "constant") return ruleFailure(record, "存在消去的见证参数必须是一个常项");
      const name = match.term.name;
      const openAssumptions = openAssumptionRecords(record, allProofRecords, openerByPath).map((entry) => entry.ast);
      if (
        collectConstants(source).has(name) ||
        collectConstants(result).has(name) ||
        constantAppears([...premises.map((entry) => entry.ast), ...openAssumptions], name)
      ) {
        return ruleFailure(record, `见证参数 ${name} 出现在存在式、结论、前提或尚未解除的假设中`);
      }
      return null;
    }

    case "identity-intro": {
      const valid = citationShape(record, 0, 0) && result.kind === "equality" && termEquals(result.left, result.right);
      return valid ? null : ruleFailure(record, "只能无条件引入形如 t = t 的公式");
    }

    case "identity-elim": {
      if (!citationShape(record, 2, 0)) return ruleFailure(record, "须引用一个等同式和一个含有待替换项的公式");
      const valid = formulas.some((candidate, equalityIndex) => {
        const equality = candidate.ast;
        if (equality.kind !== "equality") return false;
        const source = formulas[1 - equalityIndex].ast;
        return (
          isSelectiveReplacement(source, result, equality.left, equality.right) ||
          isSelectiveReplacement(source, result, equality.right, equality.left)
        );
      });
      return valid ? null : ruleFailure(record, "结论须由等同项在另一所引公式中替换一次或多次得到");
    }

    case "disjunctive-syllogism": {
      if (!citationShape(record, 2, 0)) return ruleFailure(record, "须引用一个析取式和一个析取支的否定");
      const valid = formulaAsts.some((candidate, index) => {
        if (!isBinary(candidate, "or")) return false;
        const negation = formulaAsts[1 - index];
        return (
          (isNegationOf(negation, candidate.left) && formulasMatch(result, candidate.right)) ||
          (isNegationOf(negation, candidate.right) && formulasMatch(result, candidate.left))
        );
      });
      return valid ? null : ruleFailure(record, "被否定的析取支与结论不匹配");
    }

    case "modus-tollens": {
      if (!citationShape(record, 2, 0) || result.kind !== "not") {
        return ruleFailure(record, "须引用一个条件式及其后件的否定");
      }
      const valid = formulaAsts.some((candidate, index) => {
        const negation = formulaAsts[1 - index];
        return (
          isBinary(candidate, "implies") &&
          isNegationOf(negation, candidate.right) &&
          formulasMatch(result.value, candidate.left)
        );
      });
      return valid ? null : ruleFailure(record, "引用的公式不构成否定后件式");
    }

    case "double-negation": {
      const source = formulaAsts[0];
      const valid =
        citationShape(record, 1, 0) &&
        source.kind === "not" &&
        source.value.kind === "not" &&
        formulasMatch(source.value.value, result);
      return valid ? null : ruleFailure(record, "须从双重否定式推出其内部公式");
    }

    case "excluded-middle": {
      if (!citationShape(record, 0, 2)) return ruleFailure(record, "须引用两个子证明");
      const [first, second] = ranges;
      const opposite =
        isNegationOf(first.startRecord.ast, second.startRecord.ast) ||
        isNegationOf(second.startRecord.ast, first.startRecord.ast);
      const sameConclusion = formulasMatch(first.endRecord.ast, result) && formulasMatch(second.endRecord.ast, result);
      return opposite && sameConclusion
        ? null
        : ruleFailure(record, "两个子证明须分别假设 A 与 ¬A，并都得到当前结论");
    }

    case "demorgan":
      return citationShape(record, 1, 0) && isDeMorganRewrite(formulaAsts[0], result)
        ? null
        : ruleFailure(record, "只允许德摩根律的四种直接改写");

    case "quantifier-conversion":
      return citationShape(record, 1, 0) && isQuantifierConversion(formulaAsts[0], result)
        ? null
        : ruleFailure(record, "只允许量词与否定之间的四种直接转换");

    default:
      return error("rule", "UNKNOWN_RULE", "请选择一个有效的推理规则", record);
  }
}

function pickEarlierProblem(current, candidate) {
  if (!candidate) return current;
  if (!current) return candidate;
  return candidate.lineNumber < current.lineNumber ? candidate : current;
}

function lastLineAtSubproofDepth(startRecord, proofRecords) {
  let last = startRecord;
  for (let index = startRecord.index + 1; index < proofRecords.length; index += 1) {
    const candidate = proofRecords[index];
    if (!isPrefix(startRecord.path, candidate.path)) break;
    if (
      candidate.path.length === startRecord.path.length &&
      candidate.path.every((component, pathIndex) => component === startRecord.path[pathIndex])
    ) {
      last = candidate;
    }
  }
  return last;
}

/**
 * Check a complete proof document. Premises occupy the first numbered rows;
 * proof lines continue that numbering. Nothing is checked until this function
 * is called. On failure, the problem on the earliest numbered row is returned.
 */
export function checkProof(document) {
  if (!document || !Array.isArray(document.premises) || !Array.isArray(document.lines)) {
    return failure(error("document", "INVALID_DOCUMENT", "证明须包含 premises 与 lines 两个数组"));
  }
  if (document.lines.length === 0) {
    return failure(error("document", "EMPTY_PROOF", "请至少添加一个证明步骤"));
  }

  const premiseRecords = document.premises.map((item, index) => ({
    type: "premise",
    index,
    number: index + 1,
    source: typeof item === "string" ? item : item?.formula,
    path: [],
  }));
  const proofRecords = document.lines.map((line, index) => ({
    type: "line",
    index,
    number: premiseRecords.length + index + 1,
    source: line?.formula,
    raw: line ?? {},
    path: normalizePath(line?.path),
    rule: normalizeRule(line),
    declaredAssumption: line?.isAssumption === true,
  }));

  // First gather the earliest structural, syntactic, or signature problem.
  // We do not return it yet: an earlier proof row may contain a bad citation or
  // an invalid inference, and the editor promises to report that row first.
  let foundationalProblem = null;
  const openerByPath = new Map();
  let previousPath = [];
  for (const record of proofRecords) {
    let problem = null;
    if (record.path == null) {
      problem = error("structure", "INVALID_PATH", "子证明路径必须是一个由标识符组成的数组", record);
    } else if (record.declaredAssumption && record.rule && record.rule !== "assumption") {
      problem = error("structure", "ASSUMPTION_RULE_CONFLICT", "假设行不能同时使用其他推理规则", record);
    } else {
      const common = commonPrefixLength(previousPath, record.path);
      const introduced = record.path.length - common;
      const isAssumption = record.rule === "assumption";
      if (introduced > 1) {
        problem = error("structure", "SKIPPED_SUBPROOF_LEVEL", "一行只能新开一层子证明", record);
      } else if (introduced === 1 && !isAssumption) {
        problem = error("structure", "MISSING_ASSUMPTION", "子证明的第一行必须标为假设", record);
      } else if (introduced === 0 && isAssumption) {
        problem = error("structure", "ASSUMPTION_WITHOUT_NEW_SCOPE", "假设必须开启一个新的子证明", record);
      } else if (introduced === 1) {
        const key = pathKey(record.path);
        if (openerByPath.has(key)) {
          problem = error("structure", "REOPENED_SUBPROOF", "已经结束的子证明不能重新打开", record);
        } else {
          openerByPath.set(key, record.number);
        }
      }
    }
    if (problem) {
      foundationalProblem = pickEarlierProblem(foundationalProblem, problem);
      break;
    }
    previousPath = record.path;
  }

  const allRecords = [...premiseRecords, ...proofRecords];
  for (const record of allRecords) {
    let problem = null;
    if (typeof record.source !== "string") {
      problem = error("syntax", "FORMULA_NOT_STRING", "公式必须是字符串", record);
    } else {
      try {
        record.ast = parseFormula(record.source);
      } catch (caught) {
        problem = error("syntax", caught.code ?? "SYNTAX_ERROR", caught.message, record, {
          position: caught.position,
          end: caught.end,
        });
      }
    }
    foundationalProblem = pickEarlierProblem(foundationalProblem, problem);
  }

  const parsedRecords = allRecords.filter((record) => record.ast != null);
  const signature = validateSignatures(parsedRecords.map((record) => record.ast));
  if (!signature.valid) {
    const warning = signature.warnings[0];
    const record = parsedRecords[warning.formulaIndex];
    foundationalProblem = pickEarlierProblem(
      foundationalProblem,
      error(
        "signature",
        warning.code,
        `${warning.kind === "predicate" ? "谓词" : "函数"} ${warning.name} 的元数不一致：首次为 ${warning.expectedArity}，此处为 ${warning.actualArity}`,
        record,
        {
          formulaIndex: allRecords.indexOf(record),
          symbolKind: warning.kind,
          symbolName: warning.name,
          expectedArity: warning.expectedArity,
          actualArity: warning.actualArity,
        },
      ),
    );
  }

  const byNumber = new Map(allRecords.map((record) => [record.number, record]));
  for (const record of proofRecords) {
    if (foundationalProblem && record.number >= foundationalProblem.lineNumber) break;
    try {
      record.citations = parseCitations(record.raw.citations);
    } catch (problem) {
      return failure(error("citation", "MALFORMED_CITATION", problem.message, record));
    }
    record.references = [];
    for (const citation of record.citations) {
      if (citation.type === "line") {
        if (citation.line >= record.number) {
          return failure(error("citation", "FORWARD_REFERENCE", "只能引用当前行以前的公式", record, { citation }));
        }
        const cited = byNumber.get(citation.line);
        if (!cited) {
          return failure(error("citation", "UNKNOWN_LINE", `不存在第 ${citation.line} 行`, record, { citation }));
        }
        if (cited.type === "line" && !isPrefix(cited.path, record.path)) {
          return failure(error("scope", "INACCESSIBLE_LINE", `第 ${citation.line} 行位于已经结束或平行的子证明中`, record, { citation }));
        }
        record.references.push({ ...citation, record: cited });
        continue;
      }

      if (citation.end >= record.number) {
        return failure(error("citation", "FORWARD_REFERENCE", "只能引用当前行以前已经完成的子证明", record, { citation }));
      }
      const startRecord = byNumber.get(citation.start);
      const endRecord = byNumber.get(citation.end);
      if (!startRecord || !endRecord) {
        return failure(error("citation", "UNKNOWN_LINE", `子证明范围 ${citation.start}-${citation.end} 含有不存在的行`, record, { citation }));
      }
      if (startRecord.type !== "line" || endRecord.type !== "line" || startRecord.rule !== "assumption") {
        return failure(error("citation", "INVALID_SUBPROOF", `范围 ${citation.start}-${citation.end} 必须从一个假设行开始`, record, { citation }));
      }
      if (!startRecord.path.length || !startRecord.path.every((item, index) => endRecord.path[index] === item) || endRecord.path.length !== startRecord.path.length) {
        return failure(error("citation", "INVALID_SUBPROOF", `第 ${citation.end} 行不是该子证明自身层级中的结论`, record, { citation }));
      }
      const parentPath = startRecord.path.slice(0, -1);
      if (!isPrefix(parentPath, record.path)) {
        return failure(error("scope", "INACCESSIBLE_SUBPROOF", `子证明 ${citation.start}-${citation.end} 不在当前证明的父层级中`, record, { citation }));
      }
      if (isPrefix(startRecord.path, record.path)) {
        return failure(error("scope", "OPEN_SUBPROOF", `子证明 ${citation.start}-${citation.end} 尚未结束`, record, { citation }));
      }
      const actualEnd = lastLineAtSubproofDepth(startRecord, proofRecords);
      if (endRecord !== actualEnd) {
        return failure(
          error(
            "citation",
            "INVALID_SUBPROOF",
            `子证明 ${citation.start}-${citation.end} 的末行应为第 ${actualEnd.number} 行`,
            record,
            { citation, expectedEnd: actualEnd.number },
          ),
        );
      }
      record.references.push({ ...citation, startRecord, endRecord });
    }
    const problem = checkRule(record, premiseRecords, proofRecords, openerByPath);
    if (problem) return failure(problem);
  }

  if (foundationalProblem) return failure(foundationalProblem);

  return {
    ok: true,
    premiseCount: premiseRecords.length,
    lineCount: proofRecords.length,
    conclusion: proofRecords.at(-1)?.ast ?? null,
    signature: {
      predicates: Object.fromEntries(signature.predicates),
      functions: Object.fromEntries(signature.functions),
    },
  };
}
