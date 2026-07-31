const LETTER_TERMS = Object.freeze(["S", "M", "P", "Q", "R"]);

export const FITCH_RULES = Object.freeze({
  premise: "前提",
  assumption: "假设",
  "forall-elim": "全称消去",
  "forall-intro": "全称引入",
  "exists-elim": "存在消去",
  "exists-intro": "存在引入",
  "implies-elim": "条件消去",
  "implies-intro": "条件引入",
  "and-elim": "合取消去",
  "and-intro": "合取引入",
  "not-elim": "否定消去",
  "not-intro": "否定引入",
  "bottom-elim": "爆炸律",
});

const variable = (name) => ({ kind: "variable", name });
const constant = (name) => ({ kind: "constant", name });
const predicate = (predicateIndex, argument) => ({
  kind: "predicate",
  predicate: predicateIndex,
  argument,
});
const not = (body) => ({ kind: "not", body });
const and = (left, right) => ({ kind: "and", left, right });
const implies = (left, right) => ({ kind: "implies", left, right });
const forall = (name, body) => ({ kind: "forall", variable: name, body });
const exists = (name, body) => ({ kind: "exists", variable: name, body });
const bottom = () => ({ kind: "bottom" });

function cloneFormula(formula) {
  return structuredClone(formula);
}

export function categoricalToFormula(statement, variableName = "x") {
  const argument = variable(variableName);
  const subject = predicate(statement.subject, argument);
  const target = predicate(statement.predicate, argument);

  switch (statement.form) {
    case "A":
      return forall(variableName, implies(subject, target));
    case "E":
      return forall(variableName, implies(subject, not(target)));
    case "I":
      return exists(variableName, and(subject, target));
    case "O":
      return exists(variableName, and(subject, not(target)));
    default:
      throw new Error(`未知的直言命题类型：${statement.form}`);
  }
}

function formulaKey(formula) {
  switch (formula.kind) {
    case "predicate":
      return `p:${formula.predicate}:${formula.argument.kind}:${formula.argument.name}`;
    case "not":
      return `n(${formulaKey(formula.body)})`;
    case "and":
      return `a(${formulaKey(formula.left)},${formulaKey(formula.right)})`;
    case "implies":
      return `i(${formulaKey(formula.left)},${formulaKey(formula.right)})`;
    case "forall":
      return `u:${formula.variable}(${formulaKey(formula.body)})`;
    case "exists":
      return `e:${formula.variable}(${formulaKey(formula.body)})`;
    case "bottom":
      return "bottom";
    default:
      throw new Error(`未知的公式节点：${formula?.kind}`);
  }
}

function sameFormula(left, right) {
  return Boolean(left && right && formulaKey(left) === formulaKey(right));
}

function substituteVariable(formula, variableName, replacement) {
  switch (formula.kind) {
    case "predicate":
      return predicate(
        formula.predicate,
        formula.argument.kind === "variable" &&
          formula.argument.name === variableName
          ? { ...replacement }
          : { ...formula.argument },
      );
    case "not":
      return not(substituteVariable(formula.body, variableName, replacement));
    case "and":
      return and(
        substituteVariable(formula.left, variableName, replacement),
        substituteVariable(formula.right, variableName, replacement),
      );
    case "implies":
      return implies(
        substituteVariable(formula.left, variableName, replacement),
        substituteVariable(formula.right, variableName, replacement),
      );
    case "forall":
    case "exists":
      if (formula.variable === variableName) return cloneFormula(formula);
      return {
        kind: formula.kind,
        variable: formula.variable,
        body: substituteVariable(formula.body, variableName, replacement),
      };
    case "bottom":
      return bottom();
    default:
      throw new Error(`未知的公式节点：${formula?.kind}`);
  }
}

function containsConstant(formula, name) {
  switch (formula.kind) {
    case "predicate":
      return (
        formula.argument.kind === "constant" && formula.argument.name === name
      );
    case "not":
      return containsConstant(formula.body, name);
    case "and":
    case "implies":
      return (
        containsConstant(formula.left, name) ||
        containsConstant(formula.right, name)
      );
    case "forall":
    case "exists":
      return containsConstant(formula.body, name);
    case "bottom":
      return false;
    default:
      return false;
  }
}

function formatTerm(argument) {
  return argument.name;
}

function formatWithPrecedence(formula, displayTerms, parentPrecedence = 0) {
  switch (formula.kind) {
    case "predicate":
      return `${displayTerms[formula.predicate]}(${formatTerm(formula.argument)})`;
    case "bottom":
      return "⊥";
    case "not": {
      const body = formatWithPrecedence(formula.body, displayTerms, 4);
      return `¬${body}`;
    }
    case "and": {
      const precedence = 3;
      const text = `${formatWithPrecedence(
        formula.left,
        displayTerms,
        precedence,
      )} ∧ ${formatWithPrecedence(formula.right, displayTerms, precedence)}`;
      return parentPrecedence > precedence ? `(${text})` : text;
    }
    case "implies": {
      const precedence = 2;
      const text = `${formatWithPrecedence(
        formula.left,
        displayTerms,
        precedence + 1,
      )} → ${formatWithPrecedence(formula.right, displayTerms, precedence)}`;
      return parentPrecedence > precedence ? `(${text})` : text;
    }
    case "forall":
      return `∀${formula.variable}(${formatWithPrecedence(
        formula.body,
        displayTerms,
      )})`;
    case "exists":
      return `∃${formula.variable}(${formatWithPrecedence(
        formula.body,
        displayTerms,
      )})`;
    default:
      throw new Error(`未知的公式节点：${formula?.kind}`);
  }
}

export function formatFitchFormula(
  formula,
  terms,
  { mode = "natural" } = {},
) {
  return formatWithPrecedence(
    formula,
    mode === "letters" ? LETTER_TERMS : terms,
  );
}

function pathIsPrefix(prefix, path) {
  return (
    prefix.length <= path.length &&
    prefix.every((part, index) => part === path[index])
  );
}

function pathKey(path) {
  return path.join("/");
}

class ProofBuilder {
  constructor(premises, usedPremiseIndices) {
    this.lines = [];
    this.premises = premises;
    this.premiseLines = new Map();
    this.instanceLines = [];
    this.scopeCounter = 0;

    [...usedPremiseIndices]
      .sort((left, right) => left - right)
      .forEach((premiseIndex) => {
        const line = this.add({
          formula: categoricalToFormula(premises[premiseIndex]),
          rule: "premise",
          scopePath: [],
          premiseIndex,
        });
        this.premiseLines.set(premiseIndex, line);
      });
  }

  newScope(prefix) {
    this.scopeCounter += 1;
    return `${prefix}-${this.scopeCounter}`;
  }

  add({
    formula,
    rule,
    scopePath,
    refs = [],
    ranges = [],
    premiseIndex = null,
    constantName = null,
    assumptionKind = null,
  }) {
    const line = {
      number: this.lines.length + 1,
      depth: scopePath.length,
      scopePath: [...scopePath],
      formula: cloneFormula(formula),
      rule,
      ruleLabel: FITCH_RULES[rule],
      refs: refs.map(({ number }) => number),
      ranges: ranges.map(({ start, end }) => [start.number, end.number]),
      premiseIndex,
      constant: constantName,
      assumptionKind,
    };
    this.lines.push(line);
    return line;
  }

  instantiate(premiseIndex, constantName, scopePath) {
    const accessible = this.instanceLines.find(
      (entry) =>
        entry.premiseIndex === premiseIndex &&
        entry.constantName === constantName &&
        pathIsPrefix(entry.scopePath, scopePath),
    );
    if (accessible) return accessible.line;

    const premiseLine = this.premiseLines.get(premiseIndex);
    if (!premiseLine) {
      throw new Error(`证明中缺少前提 ${premiseIndex + 1}。`);
    }
    const universal = premiseLine.formula;
    if (universal.kind !== "forall") {
      throw new Error("只有全称前提可以使用 ∀E。");
    }
    const instance = substituteVariable(
      universal.body,
      universal.variable,
      constant(constantName),
    );
    const line = this.add({
      formula: instance,
      rule: "forall-elim",
      scopePath,
      refs: [premiseLine],
      constantName,
    });
    this.instanceLines.push({
      premiseIndex,
      constantName,
      scopePath: [...scopePath],
      line,
    });
    return line;
  }
}

function literalKey(term, positive = true) {
  return `${positive ? "+" : "-"}${term}`;
}

function atomAt(term, constantName) {
  return predicate(term, constant(constantName));
}

function literalFormula(term, positive, constantName) {
  const atom = atomAt(term, constantName);
  return positive ? atom : not(atom);
}

function statementMatches(left, right) {
  return (
    left.form === right.form &&
    left.subject === right.subject &&
    left.predicate === right.predicate
  );
}

function aEdges(premises) {
  return premises
    .map((item, premiseIndex) => ({ ...item, premiseIndex }))
    .filter(({ form }) => form === "A")
    .map(({ subject, predicate: target, premiseIndex }) => ({
      from: subject,
      to: target,
      premiseIndex,
    }));
}

function enumeratePathsFromSeed(seed, target, edges, termCount) {
  const paths = [];

  const visit = (current, visited, route) => {
    if (current === target) {
      paths.push({ seed: { ...seed }, edges: [...route] });
      return;
    }
    if (route.length >= termCount - 1) return;

    for (const edge of edges) {
      if (edge.from !== current || visited.has(edge.to)) continue;
      const nextVisited = new Set(visited);
      nextVisited.add(edge.to);
      visit(edge.to, nextVisited, [...route, edge]);
    }
  };

  visit(seed.term, new Set([seed.term]), []);
  return paths;
}

function enumeratePaths(seeds, target, edges, termCount) {
  const paths = seeds.flatMap((seed) =>
    enumeratePathsFromSeed(seed, target, edges, termCount),
  );
  const seen = new Set();
  return paths.filter((path) => {
    const key = `${path.seed.source}:${path.seed.term}:${path.edges
      .map(({ premiseIndex }) => premiseIndex)
      .join(",")}`;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

function contradictionPlans(
  positiveSeeds,
  negativeTerms,
  premises,
  termCount,
) {
  const edges = aEdges(premises);
  const plans = [];

  for (const negativeTerm of negativeTerms) {
    for (const positivePath of enumeratePaths(
      positiveSeeds,
      negativeTerm,
      edges,
      termCount,
    )) {
      plans.push({
        kind: "negative-seed-conflict",
        positivePath,
        negativeTerm,
      });
    }
  }

  premises.forEach((item, premiseIndex) => {
    if (item.form !== "E") return;
    const leftPaths = enumeratePaths(
      positiveSeeds,
      item.subject,
      edges,
      termCount,
    );
    const rightPaths = enumeratePaths(
      positiveSeeds,
      item.predicate,
      edges,
      termCount,
    );
    for (const leftPath of leftPaths) {
      for (const rightPath of rightPaths) {
        plans.push({
          kind: "e-conflict",
          leftPath,
          rightPath,
          premiseIndex,
        });
      }
    }
  });

  return plans;
}

function directNegativePlans(
  positiveSeeds,
  negativeTerms,
  target,
  premises,
  termCount,
) {
  const plans = [];
  if (negativeTerms.includes(target)) {
    plans.push({ kind: "negative-seed", target });
  }

  const edges = aEdges(premises);
  premises.forEach((item, premiseIndex) => {
    if (item.form !== "E" || item.predicate !== target) return;
    for (const path of enumeratePaths(
      positiveSeeds,
      item.subject,
      edges,
      termCount,
    )) {
      plans.push({
        kind: "direct-e",
        path,
        premiseIndex,
        target,
      });
    }
  });
  return plans;
}

function negativePlans(
  positiveSeeds,
  negativeTerms,
  target,
  premises,
  termCount,
) {
  const plans = directNegativePlans(
    positiveSeeds,
    negativeTerms,
    target,
    premises,
    termCount,
  );
  const assumedSeed = { term: target, source: "assumed" };
  const indirect = contradictionPlans(
    [...positiveSeeds, assumedSeed],
    negativeTerms,
    premises,
    termCount,
  );
  for (const contradiction of indirect) {
    plans.push({
      kind: "not-intro",
      target,
      contradiction,
    });
  }
  return plans;
}

function existentialSpec(item, premiseIndex) {
  if (item.form === "I") {
    return {
      premiseIndex,
      positiveTerms: [...new Set([item.subject, item.predicate])],
      negativeTerms: [],
    };
  }
  if (item.form === "O") {
    return {
      premiseIndex,
      positiveTerms: [item.subject],
      negativeTerms: [item.predicate],
    };
  }
  return null;
}

function collectPremiseIndices(value, result = new Set(), seen = new Set()) {
  if (!value || typeof value !== "object" || seen.has(value)) return result;
  seen.add(value);
  if (Number.isInteger(value.premiseIndex)) result.add(value.premiseIndex);
  if (Array.isArray(value)) {
    value.forEach((item) => collectPremiseIndices(item, result, seen));
  } else {
    Object.values(value).forEach((item) =>
      collectPremiseIndices(item, result, seen),
    );
  }
  return result;
}

function collectSeedNeeds(value, needs, seen = new Set()) {
  if (!value || typeof value !== "object" || seen.has(value)) return;
  seen.add(value);

  if (value.seed?.source === "base") {
    needs.positive.add(value.seed.term);
  }
  if (value.kind === "negative-seed") {
    needs.negative.add(value.target);
  }
  if (value.kind === "negative-seed-conflict") {
    needs.negative.add(value.negativeTerm);
  }

  if (Array.isArray(value)) {
    value.forEach((item) => collectSeedNeeds(item, needs, seen));
  } else {
    Object.values(value).forEach((item) =>
      collectSeedNeeds(item, needs, seen),
    );
  }
}

function seedLinesForWitness(
  builder,
  witnessLine,
  source,
  plan,
  constantName,
  scopePath,
) {
  const facts = new Map();
  const needs = { positive: new Set(), negative: new Set() };
  collectSeedNeeds(plan, needs);
  const item = builder.premises[source.premiseIndex];
  const conjunction = witnessLine.formula;

  const addSeed = (term, positive, side) => {
    const key = literalKey(term, positive);
    if (facts.has(key)) return;
    const expected = literalFormula(term, positive, constantName);
    const conjunct = side === "left" ? conjunction.left : conjunction.right;
    if (!sameFormula(conjunct, expected)) {
      throw new Error("存在见证与待提取的合取支不一致。");
    }
    const line = builder.add({
      formula: expected,
      rule: "and-elim",
      scopePath,
      refs: [witnessLine],
    });
    facts.set(key, line);
  };

  if (item.form === "I") {
    if (needs.positive.has(item.subject)) {
      addSeed(item.subject, true, "left");
    }
    if (needs.positive.has(item.predicate)) {
      const side = item.predicate === item.subject ? "left" : "right";
      addSeed(item.predicate, true, side);
    }
  } else {
    if (needs.positive.has(item.subject)) {
      addSeed(item.subject, true, "left");
    }
    if (needs.negative.has(item.predicate)) {
      addSeed(item.predicate, false, "right");
    }
  }
  return facts;
}

function derivePositivePath(
  builder,
  path,
  facts,
  constantName,
  scopePath,
) {
  let currentLine = facts.get(literalKey(path.seed.term, true));
  if (!currentLine) {
    throw new Error(`证明中缺少正文字 ${path.seed.term} 的起点。`);
  }

  for (const edge of path.edges) {
    const targetKey = literalKey(edge.to, true);
    const cached = facts.get(targetKey);
    if (cached) {
      currentLine = cached;
      continue;
    }
    const conditional = builder.instantiate(
      edge.premiseIndex,
      constantName,
      scopePath,
    );
    currentLine = builder.add({
      formula: atomAt(edge.to, constantName),
      rule: "implies-elim",
      scopePath,
      refs: [conditional, currentLine],
    });
    facts.set(targetKey, currentLine);
  }
  return currentLine;
}

function deriveBasePathsBeforeNegation(
  builder,
  value,
  facts,
  constantName,
  scopePath,
  seen = new Set(),
) {
  if (!value || typeof value !== "object" || seen.has(value)) return;
  seen.add(value);
  if (value.seed?.source === "base" && Array.isArray(value.edges)) {
    derivePositivePath(builder, value, facts, constantName, scopePath);
    return;
  }
  if (Array.isArray(value)) {
    value.forEach((item) =>
      deriveBasePathsBeforeNegation(
        builder,
        item,
        facts,
        constantName,
        scopePath,
        seen,
      ),
    );
  } else {
    Object.values(value).forEach((item) =>
      deriveBasePathsBeforeNegation(
        builder,
        item,
        facts,
        constantName,
        scopePath,
        seen,
      ),
    );
  }
}

function deriveContradiction(
  builder,
  plan,
  facts,
  constantName,
  scopePath,
) {
  if (plan.kind === "negative-seed-conflict") {
    const positiveLine = derivePositivePath(
      builder,
      plan.positivePath,
      facts,
      constantName,
      scopePath,
    );
    const negativeLine = facts.get(literalKey(plan.negativeTerm, false));
    if (!negativeLine) throw new Error("证明中缺少负文字见证。");
    return builder.add({
      formula: bottom(),
      rule: "not-elim",
      scopePath,
      refs: [negativeLine, positiveLine],
    });
  }

  if (plan.kind === "e-conflict") {
    const leftLine = derivePositivePath(
      builder,
      plan.leftPath,
      facts,
      constantName,
      scopePath,
    );
    const rightLine = derivePositivePath(
      builder,
      plan.rightPath,
      facts,
      constantName,
      scopePath,
    );
    const conditional = builder.instantiate(
      plan.premiseIndex,
      constantName,
      scopePath,
    );
    const premise = builder.premises[plan.premiseIndex];
    const negativeLine = builder.add({
      formula: not(atomAt(premise.predicate, constantName)),
      rule: "implies-elim",
      scopePath,
      refs: [conditional, leftLine],
    });
    return builder.add({
      formula: bottom(),
      rule: "not-elim",
      scopePath,
      refs: [negativeLine, rightLine],
    });
  }

  throw new Error(`未知的矛盾方案：${plan.kind}`);
}

function deriveNegative(
  builder,
  plan,
  facts,
  constantName,
  scopePath,
) {
  if (plan.kind === "negative-seed") {
    const line = facts.get(literalKey(plan.target, false));
    if (!line) throw new Error("证明中缺少负文字见证。");
    return line;
  }

  if (plan.kind === "direct-e") {
    const positiveLine = derivePositivePath(
      builder,
      plan.path,
      facts,
      constantName,
      scopePath,
    );
    const conditional = builder.instantiate(
      plan.premiseIndex,
      constantName,
      scopePath,
    );
    const line = builder.add({
      formula: not(atomAt(plan.target, constantName)),
      rule: "implies-elim",
      scopePath,
      refs: [conditional, positiveLine],
    });
    facts.set(literalKey(plan.target, false), line);
    return line;
  }

  if (plan.kind === "not-intro") {
    deriveBasePathsBeforeNegation(
      builder,
      plan.contradiction,
      facts,
      constantName,
      scopePath,
    );
    const childScope = [...scopePath, builder.newScope("neg")];
    const assumptionLine = builder.add({
      formula: atomAt(plan.target, constantName),
      rule: "assumption",
      scopePath: childScope,
      assumptionKind: "negation",
    });
    const childFacts = new Map(facts);
    childFacts.set(literalKey(plan.target, true), assumptionLine);
    const contradiction = deriveContradiction(
      builder,
      plan.contradiction,
      childFacts,
      constantName,
      childScope,
    );
    const negativeLine = builder.add({
      formula: not(atomAt(plan.target, constantName)),
      rule: "not-intro",
      scopePath,
      ranges: [{ start: assumptionLine, end: contradiction }],
    });
    facts.set(literalKey(plan.target, false), negativeLine);
    return negativeLine;
  }

  throw new Error(`未知的否定方案：${plan.kind}`);
}

function finishUniversalProof(
  builder,
  conclusion,
  assumptionLine,
  resultLine,
  scopePath,
  constantName,
) {
  const conditional = builder.add({
    formula: implies(
      atomAt(conclusion.subject, constantName),
      conclusion.form === "A"
        ? atomAt(conclusion.predicate, constantName)
        : not(atomAt(conclusion.predicate, constantName)),
    ),
    rule: "implies-intro",
    scopePath: [],
    ranges: [{ start: assumptionLine, end: resultLine }],
  });
  builder.add({
    formula: categoricalToFormula(conclusion),
    rule: "forall-intro",
    scopePath: [],
    refs: [conditional],
    constantName,
  });
  return builder.lines;
}

function materializeUniversalPlan(premises, conclusion, plan) {
  const used = collectPremiseIndices(plan);
  const builder = new ProofBuilder(premises, used);
  const constantName = "a";
  const scopePath = [builder.newScope("universal")];
  const assumptionLine = builder.add({
    formula: atomAt(conclusion.subject, constantName),
    rule: "assumption",
    scopePath,
    assumptionKind: "conditional",
  });
  const facts = new Map([
    [literalKey(conclusion.subject, true), assumptionLine],
  ]);
  let resultLine;

  if (plan.kind === "universal-a-path") {
    resultLine = derivePositivePath(
      builder,
      plan.path,
      facts,
      constantName,
      scopePath,
    );
  } else if (plan.kind === "universal-a-bottom") {
    const contradiction = deriveContradiction(
      builder,
      plan.contradiction,
      facts,
      constantName,
      scopePath,
    );
    resultLine = builder.add({
      formula: atomAt(conclusion.predicate, constantName),
      rule: "bottom-elim",
      scopePath,
      refs: [contradiction],
    });
  } else if (plan.kind === "universal-e-direct") {
    resultLine = deriveNegative(
      builder,
      plan.negative,
      facts,
      constantName,
      scopePath,
    );
  } else if (plan.kind === "universal-e-not") {
    resultLine = deriveNegative(
      builder,
      plan.negative,
      facts,
      constantName,
      scopePath,
    );
  } else if (plan.kind === "universal-e-bottom") {
    const contradiction = deriveContradiction(
      builder,
      plan.contradiction,
      facts,
      constantName,
      scopePath,
    );
    resultLine = builder.add({
      formula: not(atomAt(conclusion.predicate, constantName)),
      rule: "bottom-elim",
      scopePath,
      refs: [contradiction],
    });
  } else {
    throw new Error(`未知的全称证明方案：${plan.kind}`);
  }

  finishUniversalProof(
    builder,
    conclusion,
    assumptionLine,
    resultLine,
    scopePath,
    constantName,
  );
  return builder.lines;
}

function materializeExistentialPlan(premises, conclusion, plan) {
  const used = collectPremiseIndices(plan);
  const builder = new ProofBuilder(premises, used);
  const source = plan.source;
  const sourceLine = builder.premiseLines.get(source.premiseIndex);
  const constantName = "c";
  const scopePath = [builder.newScope("witness")];
  const existentialFormula = sourceLine.formula;
  const witnessFormula = substituteVariable(
    existentialFormula.body,
    existentialFormula.variable,
    constant(constantName),
  );
  const witnessLine = builder.add({
    formula: witnessFormula,
    rule: "assumption",
    scopePath,
    constantName,
    assumptionKind: "existential",
  });
  const facts = seedLinesForWitness(
    builder,
    witnessLine,
    source,
    plan,
    constantName,
    scopePath,
  );

  let subjectLine;
  let predicateLine;

  if (plan.kind === "existential-i") {
    subjectLine = derivePositivePath(
      builder,
      plan.subjectPath,
      facts,
      constantName,
      scopePath,
    );
    predicateLine = derivePositivePath(
      builder,
      plan.predicatePath,
      facts,
      constantName,
      scopePath,
    );
  } else if (plan.kind === "existential-o") {
    subjectLine = derivePositivePath(
      builder,
      plan.subjectPath,
      facts,
      constantName,
      scopePath,
    );
    predicateLine = deriveNegative(
      builder,
      plan.negative,
      facts,
      constantName,
      scopePath,
    );
  } else {
    throw new Error(`未知的存在证明方案：${plan.kind}`);
  }

  const conjunction = builder.add({
    formula: and(
      atomAt(conclusion.subject, constantName),
      conclusion.form === "I"
        ? atomAt(conclusion.predicate, constantName)
        : not(atomAt(conclusion.predicate, constantName)),
    ),
    rule: "and-intro",
    scopePath,
    refs: [subjectLine, predicateLine],
  });
  const insideConclusion = builder.add({
    formula: categoricalToFormula(conclusion),
    rule: "exists-intro",
    scopePath,
    refs: [conjunction],
    constantName,
  });
  builder.add({
    formula: categoricalToFormula(conclusion),
    rule: "exists-elim",
    scopePath: [],
    refs: [sourceLine],
    ranges: [{ start: witnessLine, end: insideConclusion }],
    constantName,
  });
  return builder.lines;
}

function materializeInconsistentPlan(premises, conclusion, plan) {
  const used = collectPremiseIndices(plan);
  const builder = new ProofBuilder(premises, used);
  const source = plan.source;
  const sourceLine = builder.premiseLines.get(source.premiseIndex);
  const constantName = "c";
  const scopePath = [builder.newScope("witness")];
  const witnessFormula = substituteVariable(
    sourceLine.formula.body,
    sourceLine.formula.variable,
    constant(constantName),
  );
  const witnessLine = builder.add({
    formula: witnessFormula,
    rule: "assumption",
    scopePath,
    constantName,
    assumptionKind: "existential",
  });
  const facts = seedLinesForWitness(
    builder,
    witnessLine,
    source,
    plan,
    constantName,
    scopePath,
  );
  const contradiction = deriveContradiction(
    builder,
    plan.contradiction,
    facts,
    constantName,
    scopePath,
  );
  const outsideBottom = builder.add({
    formula: bottom(),
    rule: "exists-elim",
    scopePath: [],
    refs: [sourceLine],
    ranges: [{ start: witnessLine, end: contradiction }],
    constantName,
  });
  builder.add({
    formula: categoricalToFormula(conclusion),
    rule: "bottom-elim",
    scopePath: [],
    refs: [outsideBottom],
  });
  return builder.lines;
}

function materializeExactPremise(premises, plan) {
  const builder = new ProofBuilder(premises, new Set([plan.premiseIndex]));
  return builder.lines;
}

function proofScore(lines) {
  return [
    lines.length,
    Math.max(...lines.map(({ depth }) => depth), 0),
    new Set(
      lines
        .filter(({ premiseIndex }) => premiseIndex !== null)
        .map(({ premiseIndex }) => premiseIndex),
    ).size,
  ];
}

function compareScores(left, right) {
  const leftScore = proofScore(left);
  const rightScore = proofScore(right);
  for (let index = 0; index < leftScore.length; index += 1) {
    if (leftScore[index] !== rightScore[index]) {
      return leftScore[index] - rightScore[index];
    }
  }
  return 0;
}

function plansForConclusion(premises, conclusion, termCount) {
  const plans = [];
  premises.forEach((item, premiseIndex) => {
    if (statementMatches(item, conclusion)) {
      plans.push({ kind: "exact-premise", premiseIndex });
    }
  });

  const edges = aEdges(premises);

  if (conclusion.form === "A") {
    const seed = { term: conclusion.subject, source: "base" };
    for (const path of enumeratePaths(
      [seed],
      conclusion.predicate,
      edges,
      termCount,
    )) {
      plans.push({ kind: "universal-a-path", path });
    }
    for (const contradiction of contradictionPlans(
      [seed],
      [],
      premises,
      termCount,
    )) {
      plans.push({ kind: "universal-a-bottom", contradiction });
    }
  }

  if (conclusion.form === "E") {
    const seed = { term: conclusion.subject, source: "base" };
    for (const negative of directNegativePlans(
      [seed],
      [],
      conclusion.predicate,
      premises,
      termCount,
    )) {
      plans.push({ kind: "universal-e-direct", negative });
    }
    for (const contradiction of contradictionPlans(
      [seed],
      [],
      premises,
      termCount,
    )) {
      plans.push({ kind: "universal-e-bottom", contradiction });
    }
    for (const negative of negativePlans(
      [seed],
      [],
      conclusion.predicate,
      premises,
      termCount,
    ).filter(({ kind }) => kind === "not-intro")) {
      plans.push({ kind: "universal-e-not", negative });
    }
  }

  const existentialSources = premises
    .map((item, premiseIndex) => existentialSpec(item, premiseIndex))
    .filter(Boolean);

  if (conclusion.form === "I") {
    for (const source of existentialSources) {
      const seeds = source.positiveTerms.map((term) => ({
        term,
        source: "base",
      }));
      const subjectPaths = enumeratePaths(
        seeds,
        conclusion.subject,
        edges,
        termCount,
      );
      const predicatePaths = enumeratePaths(
        seeds,
        conclusion.predicate,
        edges,
        termCount,
      );
      for (const subjectPath of subjectPaths) {
        for (const predicatePath of predicatePaths) {
          plans.push({
            kind: "existential-i",
            source,
            subjectPath,
            predicatePath,
          });
        }
      }
    }
  }

  if (conclusion.form === "O") {
    for (const source of existentialSources) {
      const seeds = source.positiveTerms.map((term) => ({
        term,
        source: "base",
      }));
      const subjectPaths = enumeratePaths(
        seeds,
        conclusion.subject,
        edges,
        termCount,
      );
      const negatives = negativePlans(
        seeds,
        source.negativeTerms,
        conclusion.predicate,
        premises,
        termCount,
      );
      for (const subjectPath of subjectPaths) {
        for (const negative of negatives) {
          plans.push({
            kind: "existential-o",
            source,
            subjectPath,
            negative,
          });
        }
      }
    }
  }

  for (const source of existentialSources) {
    const seeds = source.positiveTerms.map((term) => ({
      term,
      source: "base",
    }));
    for (const contradiction of contradictionPlans(
      seeds,
      source.negativeTerms,
      premises,
      termCount,
    )) {
      plans.push({
        kind: "inconsistent",
        source,
        contradiction,
      });
    }
  }

  return plans;
}

function materializePlan(premises, conclusion, plan) {
  if (plan.kind === "exact-premise") {
    return materializeExactPremise(premises, plan);
  }
  if (plan.kind === "inconsistent") {
    return materializeInconsistentPlan(premises, conclusion, plan);
  }
  if (plan.kind.startsWith("universal-")) {
    return materializeUniversalPlan(premises, conclusion, plan);
  }
  if (plan.kind.startsWith("existential-")) {
    return materializeExistentialPlan(premises, conclusion, plan);
  }
  throw new Error(`未知的证明方案：${plan.kind}`);
}

export function buildFitchProof(premises, conclusion, termCount) {
  const candidates = [];
  const errors = [];

  for (const plan of plansForConclusion(premises, conclusion, termCount)) {
    try {
      const lines = materializePlan(premises, conclusion, plan);
      const proof = {
        kind: "first-order",
        lines,
        usedRules: [...new Set(lines.map(({ rule }) => rule))],
      };
      if (verifyFitchProof(proof, premises, conclusion, termCount)) {
        candidates.push(proof);
      }
    } catch (error) {
      errors.push(error);
    }
  }

  candidates.sort((left, right) => compareScores(left.lines, right.lines));
  if (candidates.length === 0) {
    const detail = errors[0] ? `：${errors[0].message}` : "";
    throw new Error(`没有找到标准一阶 Fitch 证明${detail}`);
  }
  return candidates[0];
}

function isWellFormedFormula(formula, termCount, bound = new Set()) {
  if (!formula || typeof formula !== "object") return false;
  switch (formula.kind) {
    case "predicate":
      return (
        Number.isInteger(formula.predicate) &&
        formula.predicate >= 0 &&
        formula.predicate < termCount &&
        ["variable", "constant"].includes(formula.argument?.kind) &&
        typeof formula.argument.name === "string" &&
        (formula.argument.kind === "constant" ||
          bound.has(formula.argument.name))
      );
    case "not":
      return isWellFormedFormula(formula.body, termCount, bound);
    case "and":
    case "implies":
      return (
        isWellFormedFormula(formula.left, termCount, bound) &&
        isWellFormedFormula(formula.right, termCount, bound)
      );
    case "forall":
    case "exists": {
      if (typeof formula.variable !== "string") return false;
      const next = new Set(bound);
      next.add(formula.variable);
      return isWellFormedFormula(formula.body, termCount, next);
    }
    case "bottom":
      return true;
    default:
      return false;
  }
}

function validateScopeSequence(lines) {
  const closed = new Set();
  let previous = [];

  for (const line of lines) {
    const current = line.scopePath;
    let common = 0;
    while (
      common < previous.length &&
      common < current.length &&
      previous[common] === current[common]
    ) {
      common += 1;
    }
    for (let index = previous.length; index > common; index -= 1) {
      closed.add(pathKey(previous.slice(0, index)));
    }
    if (current.length > common + 1) return false;
    if (
      current.length === common + 1 &&
      (line.rule !== "assumption" || closed.has(pathKey(current)))
    ) {
      return false;
    }
    if (closed.has(pathKey(current))) return false;
    previous = current;
  }
  return true;
}

function scopeBounds(lines) {
  const bounds = new Map();
  for (const line of lines) {
    for (let depth = 1; depth <= line.scopePath.length; depth += 1) {
      const key = pathKey(line.scopePath.slice(0, depth));
      const current = bounds.get(key);
      if (!current) {
        bounds.set(key, {
          path: line.scopePath.slice(0, depth),
          start: line.number,
          end: line.number,
        });
      } else {
        current.end = line.number;
      }
    }
  }
  return bounds;
}

function visibleReference(reference, line) {
  return pathIsPrefix(reference.scopePath, line.scopePath);
}

function rangeMatchesChild(range, line, byNumber, bounds) {
  const [startNumber, endNumber] = range;
  const start = byNumber.get(startNumber);
  const end = byNumber.get(endNumber);
  if (!start || !end || start.rule !== "assumption") return false;
  if (!sameFormula(end.formula, byNumber.get(endNumber).formula)) return false;
  if (start.scopePath.length !== line.scopePath.length + 1) return false;
  if (!pathIsPrefix(line.scopePath, start.scopePath)) return false;
  if (pathKey(start.scopePath) !== pathKey(end.scopePath)) return false;
  const bound = bounds.get(pathKey(start.scopePath));
  return Boolean(bound && bound.start === startNumber && bound.end === endNumber);
}

function validRuleApplication(
  line,
  references,
  rangeLines,
  premises,
  allLines,
) {
  const exactRefs = (count) =>
    references.length === count && line.ranges.length === 0;
  const exactRanges = (count) =>
    rangeLines.length === count && line.refs.length === 0;

  switch (line.rule) {
    case "premise":
      return (
        exactRefs(0) &&
        line.premiseIndex !== null &&
        sameFormula(
          line.formula,
          categoricalToFormula(premises[line.premiseIndex]),
        )
      );
    case "assumption":
      return exactRefs(0) && line.premiseIndex === null;
    case "forall-elim": {
      if (!exactRefs(1) || references[0].formula.kind !== "forall") return false;
      const source = references[0].formula;
      return sameFormula(
        line.formula,
        substituteVariable(
          source.body,
          source.variable,
          constant(line.constant),
        ),
      );
    }
    case "forall-intro": {
      if (
        !exactRefs(1) ||
        line.formula.kind !== "forall" ||
        !line.constant
      ) {
        return false;
      }
      const instance = substituteVariable(
        line.formula.body,
        line.formula.variable,
        constant(line.constant),
      );
      if (!sameFormula(instance, references[0].formula)) return false;
      return !allLines.some(
        (candidate) =>
          candidate.number < line.number &&
          candidate.rule === "assumption" &&
          pathIsPrefix(candidate.scopePath, line.scopePath) &&
          containsConstant(candidate.formula, line.constant),
      );
    }
    case "exists-intro": {
      if (
        !exactRefs(1) ||
        line.formula.kind !== "exists" ||
        !line.constant
      ) {
        return false;
      }
      return sameFormula(
        references[0].formula,
        substituteVariable(
          line.formula.body,
          line.formula.variable,
          constant(line.constant),
        ),
      );
    }
    case "exists-elim": {
      if (
        line.refs.length !== 1 ||
        line.ranges.length !== 1 ||
        references[0].formula.kind !== "exists" ||
        !line.constant
      ) {
        return false;
      }
      const [start, end] = rangeLines[0];
      const expectedWitness = substituteVariable(
        references[0].formula.body,
        references[0].formula.variable,
        constant(line.constant),
      );
      if (
        !sameFormula(start.formula, expectedWitness) ||
        !sameFormula(end.formula, line.formula) ||
        containsConstant(references[0].formula, line.constant) ||
        containsConstant(line.formula, line.constant)
      ) {
        return false;
      }
      return !allLines.some(
        (candidate) =>
          candidate.number < start.number &&
          candidate.rule === "assumption" &&
          pathIsPrefix(candidate.scopePath, line.scopePath) &&
          containsConstant(candidate.formula, line.constant),
      );
    }
    case "implies-elim": {
      if (!exactRefs(2)) return false;
      const conditional = references.find(
        ({ formula }) => formula.kind === "implies",
      );
      const antecedent = references.find(
        (reference) => reference !== conditional,
      );
      return Boolean(
        conditional &&
          antecedent &&
          sameFormula(conditional.formula.left, antecedent.formula) &&
          sameFormula(conditional.formula.right, line.formula),
      );
    }
    case "implies-intro": {
      if (!exactRanges(1) || line.formula.kind !== "implies") return false;
      const [start, end] = rangeLines[0];
      return (
        sameFormula(line.formula.left, start.formula) &&
        sameFormula(line.formula.right, end.formula)
      );
    }
    case "and-elim":
      return (
        exactRefs(1) &&
        references[0].formula.kind === "and" &&
        (sameFormula(line.formula, references[0].formula.left) ||
          sameFormula(line.formula, references[0].formula.right))
      );
    case "and-intro":
      return (
        exactRefs(2) &&
        line.formula.kind === "and" &&
        sameFormula(line.formula.left, references[0].formula) &&
        sameFormula(line.formula.right, references[1].formula)
      );
    case "not-elim": {
      if (!exactRefs(2) || line.formula.kind !== "bottom") return false;
      const [first, second] = references.map(({ formula }) => formula);
      return (
        (first.kind === "not" && sameFormula(first.body, second)) ||
        (second.kind === "not" && sameFormula(second.body, first))
      );
    }
    case "not-intro": {
      if (
        !exactRanges(1) ||
        line.formula.kind !== "not" ||
        rangeLines[0][1].formula.kind !== "bottom"
      ) {
        return false;
      }
      return sameFormula(line.formula.body, rangeLines[0][0].formula);
    }
    case "bottom-elim":
      return exactRefs(1) && references[0].formula.kind === "bottom";
    default:
      return false;
  }
}

export function verifyFitchProof(
  proof,
  premises,
  conclusion,
  termCount,
) {
  if (!proof?.lines?.length) return false;
  const lines = proof.lines;
  if (!validateScopeSequence(lines)) return false;
  const byNumber = new Map(lines.map((line) => [line.number, line]));
  const bounds = scopeBounds(lines);

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    if (
      line.number !== index + 1 ||
      line.depth !== line.scopePath.length ||
      !isWellFormedFormula(line.formula, termCount) ||
      line.refs.some((reference) => reference >= line.number)
    ) {
      return false;
    }
    const references = line.refs.map((reference) => byNumber.get(reference));
    if (
      references.some(
        (reference) => !reference || !visibleReference(reference, line),
      )
    ) {
      return false;
    }
    if (
      line.ranges.some(
        (range) =>
          range[0] >= line.number ||
          range[1] >= line.number ||
          range[0] > range[1] ||
          !rangeMatchesChild(range, line, byNumber, bounds),
      )
    ) {
      return false;
    }
    const rangeLines = line.ranges.map(([start, end]) => [
      byNumber.get(start),
      byNumber.get(end),
    ]);
    if (
      !validRuleApplication(
        line,
        references,
        rangeLines,
        premises,
        lines,
      )
    ) {
      return false;
    }
  }

  const finalLine = lines.at(-1);
  return (
    finalLine.scopePath.length === 0 &&
    sameFormula(finalLine.formula, categoricalToFormula(conclusion))
  );
}

export function nestProofLines(lines) {
  const root = { kind: "scope", id: "root", children: [] };
  const nodes = new Map([["", root]]);

  for (const line of lines) {
    let parent = root;
    for (let depth = 1; depth <= line.scopePath.length; depth += 1) {
      const scope = line.scopePath.slice(0, depth);
      const key = pathKey(scope);
      if (!nodes.has(key)) {
        const node = {
          kind: "scope",
          id: scope.at(-1),
          path: scope,
          children: [],
        };
        parent.children.push(node);
        nodes.set(key, node);
      }
      parent = nodes.get(key);
    }
    parent.children.push({ kind: "line", line });
  }
  return root.children;
}
