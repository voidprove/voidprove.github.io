import {
  RULE_OPTIONS,
  checkProof,
  normalizeRuleId,
} from "./checker.mjs?v=random7";
import {
  alphaEquivalent,
  parseFormula,
} from "./parser.mjs?v=random7";

const RULE_BY_ID = new Map(RULE_OPTIONS.map((rule) => [rule.id, rule]));

function isPropositionalFormula(formula) {
  if (formula?.kind === "proposition") return true;
  if (formula?.kind === "not") return isPropositionalFormula(formula.value);
  if (formula?.kind === "binary") {
    return (
      isPropositionalFormula(formula.left) &&
      isPropositionalFormula(formula.right)
    );
  }
  return false;
}

export function analyzeRuleUsage(lines, premiseCount = 0) {
  const occurrences = [];
  lines.forEach((line, index) => {
    const id = normalizeRuleId(line?.rule, line?.isAssumption === true);
    const option = RULE_BY_ID.get(id);
    if (!option) return;
    occurrences.push({
      lineId: line?.id ?? null,
      lineIndex: index,
      lineNumber: premiseCount + index + 1,
      id,
      label: option.label,
      kind: option.kind,
    });
  });

  const derivedOccurrences = occurrences.filter(
    ({ kind }) => kind === "derived",
  );
  const derivedRuleIds = [
    ...new Set(derivedOccurrences.map(({ id }) => id)),
  ];
  return {
    occurrences,
    derivedOccurrences,
    derivedRuleIds,
    usesDerivedRules: derivedOccurrences.length > 0,
  };
}

function goalFailure(code, message, lineNumber, proofLineIndex, ruleUsage) {
  return {
    ok: false,
    error: {
      kind: "goal",
      code,
      message,
      lineNumber,
      proofLineIndex,
    },
    ruleUsage,
  };
}

export function checkChallengeProof({ premises, target, lines }) {
  const core = checkProof({ premises, lines });
  const ruleUsage = analyzeRuleUsage(
    Array.isArray(lines) ? lines : [],
    Array.isArray(premises) ? premises.length : 0,
  );
  if (!core.ok) return { ...core, ruleUsage };

  let targetAst;
  try {
    targetAst = parseFormula(target);
  } catch (cause) {
    return {
      ok: false,
      error: {
        kind: "challenge-config",
        code: "INVALID_TARGET",
        message: `测试结论不是合式公式：${cause.message}`,
        cause,
      },
      ruleUsage,
    };
  }
  if (!isPropositionalFormula(targetAst)) {
    return {
      ok: false,
      error: {
        kind: "challenge-config",
        code: "NON_PROPOSITIONAL_TARGET",
        message: "随机测试的结论必须是命题逻辑公式",
      },
      ruleUsage,
    };
  }
  for (let index = 0; index < premises.length; index += 1) {
    const premiseAst = parseFormula(premises[index]);
    if (!isPropositionalFormula(premiseAst)) {
      return {
        ok: false,
        error: {
          kind: "challenge-config",
          code: "NON_PROPOSITIONAL_PREMISE",
          message: `随机测试的第 ${index + 1} 个前提必须是命题逻辑公式`,
        },
        ruleUsage,
      };
    }
  }

  const finalIndex = lines.length - 1;
  const finalNumber = premises.length + lines.length;
  if (lines[finalIndex].path.length !== 0) {
    return goalFailure(
      "CONCLUSION_NOT_AT_ROOT",
      "目标结论须在所有子证明之外作为证明末行得到",
      finalNumber,
      finalIndex,
      ruleUsage,
    );
  }
  if (!alphaEquivalent(core.conclusion, targetAst)) {
    return goalFailure(
      "CONCLUSION_MISMATCH",
      `证明末行须为目标结论 ${target}`,
      finalNumber,
      finalIndex,
      ruleUsage,
    );
  }

  return {
    ...core,
    mode: "challenge",
    target: targetAst,
    ruleUsage,
  };
}
