import {
  RULE_OPTIONS,
  normalizeRuleId,
} from "./checker.mjs?v=review6";

export const DIFFICULTY_BANDS = Object.freeze([
  "direct",
  "light",
  "substantial",
]);

// Keep every tuning knob here: changing the score or output mix should not
// require touching the generator or any proof template.
const DEFAULT_POLICY_VALUES = Object.freeze({
  version: "weighted-fitch-v1",
  score: Object.freeze({
    weights: Object.freeze({
      linesAfterFirst: 1,
      subproofs: 0.5,
      multiSubproofRules: 0.75,
      extraDepth: 0.5,
      extraDistinctRules: 0,
    }),
    multiSubproofRuleIds: Object.freeze([
      "or-elim",
      "iff-intro",
      "excluded-middle",
    ]),
    normalizationScale: 5,
  }),
  thresholds: Object.freeze({
    lightMaxInclusive: 5,
  }),
  bandWeights: Object.freeze({
    direct: 30,
    light: 20,
    substantial: 50,
  }),
  generation: Object.freeze({
    maxAttemptsPerBand: 64,
    maxMetavariableAttempts: 30,
    maxOneLineCitations: 2,
  }),
});

const RULE_KIND_BY_ID = new Map(
  RULE_OPTIONS.map(({ id, kind }) => [id, kind]),
);
const MULTI_SUBPROOF_RULE_IDS = new Set([
  "or-elim",
  "iff-intro",
  "excluded-middle",
]);
const MAX_DIRECT_FORMULA_CITATIONS = 2;

function deepFreeze(value) {
  if (!value || typeof value !== "object" || Object.isFrozen(value)) {
    return value;
  }
  Object.values(value).forEach(deepFreeze);
  return Object.freeze(value);
}

function finiteNonnegative(value, label) {
  const number = Number(value);
  if (!Number.isFinite(number) || number < 0) {
    throw new RangeError(`${label} 必须是有限的非负数`);
  }
  return number;
}

function positiveInteger(value, label) {
  const number = Number(value);
  if (!Number.isInteger(number) || number <= 0) {
    throw new RangeError(`${label} 必须是正整数`);
  }
  return number;
}

function nonnegativeInteger(value, label) {
  const number = Number(value);
  if (!Number.isInteger(number) || number < 0) {
    throw new RangeError(`${label} 必须是非负整数`);
  }
  return number;
}

function normalizeBandWeights(overrides = {}) {
  const supplied = {
    ...DEFAULT_POLICY_VALUES.bandWeights,
    ...overrides,
  };
  const values = Object.fromEntries(
    DIFFICULTY_BANDS.map((band) => [
      band,
      finiteNonnegative(supplied[band], `bandWeights.${band}`),
    ]),
  );
  const scale = Math.max(...Object.values(values));
  if (scale <= 0) {
    throw new RangeError("至少一个难度层的抽样权重必须大于零");
  }
  const scaledTotal = Object.values(values).reduce(
    (sum, value) => sum + value / scale,
    0,
  );
  return Object.fromEntries(
    DIFFICULTY_BANDS.map((band) => [
      band,
      values[band] / scale / scaledTotal,
    ]),
  );
}

export function createChallengePolicy(overrides = {}) {
  if (!overrides || typeof overrides !== "object" || Array.isArray(overrides)) {
    throw new TypeError("难度策略必须是对象");
  }

  const weightOverrides = overrides.score?.weights ?? {};
  const weights = Object.fromEntries(
    Object.entries(DEFAULT_POLICY_VALUES.score.weights).map(([key, fallback]) => [
      key,
      finiteNonnegative(weightOverrides[key] ?? fallback, `score.weights.${key}`),
    ]),
  );
  const ruleIds = [
    ...(overrides.score?.multiSubproofRuleIds ??
      DEFAULT_POLICY_VALUES.score.multiSubproofRuleIds),
  ];
  if (
    ruleIds.some(
      (id) =>
        typeof id !== "string" ||
        !MULTI_SUBPROOF_RULE_IDS.has(normalizeRuleId(id)),
    )
  ) {
    throw new TypeError(
      "score.multiSubproofRuleIds 只能包含实际引用两个子证明的规则",
    );
  }

  const normalizationScale = finiteNonnegative(
    overrides.score?.normalizationScale ??
      DEFAULT_POLICY_VALUES.score.normalizationScale,
    "score.normalizationScale",
  );
  if (normalizationScale === 0) {
    throw new RangeError("score.normalizationScale 必须大于零");
  }

  const policy = {
    version: String(overrides.version ?? DEFAULT_POLICY_VALUES.version),
    score: {
      weights,
      multiSubproofRuleIds: [...new Set(ruleIds.map((id) => normalizeRuleId(id)))],
      normalizationScale,
    },
    thresholds: {
      lightMaxInclusive: finiteNonnegative(
        overrides.thresholds?.lightMaxInclusive ??
          DEFAULT_POLICY_VALUES.thresholds.lightMaxInclusive,
        "thresholds.lightMaxInclusive",
      ),
    },
    bandWeights: normalizeBandWeights(overrides.bandWeights),
    generation: {
      maxAttemptsPerBand: positiveInteger(
        overrides.generation?.maxAttemptsPerBand ??
          DEFAULT_POLICY_VALUES.generation.maxAttemptsPerBand,
        "generation.maxAttemptsPerBand",
      ),
      maxMetavariableAttempts: positiveInteger(
        overrides.generation?.maxMetavariableAttempts ??
          DEFAULT_POLICY_VALUES.generation.maxMetavariableAttempts,
        "generation.maxMetavariableAttempts",
      ),
      maxOneLineCitations: (() => {
        const value = nonnegativeInteger(
          overrides.generation?.maxOneLineCitations ??
            DEFAULT_POLICY_VALUES.generation.maxOneLineCitations,
          "generation.maxOneLineCitations",
        );
        if (value > MAX_DIRECT_FORMULA_CITATIONS) {
          throw new RangeError(
            `generation.maxOneLineCitations 不能超过 ${MAX_DIRECT_FORMULA_CITATIONS}`,
          );
        }
        return value;
      })(),
    },
  };
  if (!policy.version) throw new TypeError("难度策略版本不能为空");
  return deepFreeze(policy);
}

export const DEFAULT_CHALLENGE_POLICY = createChallengePolicy();

export function measureProofPlan(lines, policy = DEFAULT_CHALLENGE_POLICY) {
  if (!Array.isArray(lines) || lines.length === 0) {
    throw new TypeError("证明计划至少需要一行");
  }
  const canonicalRuleIds = lines.map((line) => {
    const id = normalizeRuleId(line?.rule, line?.isAssumption === true);
    if (!id) throw new TypeError(`证明计划含有未知规则：${line?.rule ?? ""}`);
    return id;
  });
  const multiSubproofRules = new Set(policy.score.multiSubproofRuleIds);
  const subproofs = canonicalRuleIds.filter((id) => id === "assumption").length;
  const maxDepth = Math.max(
    0,
    ...lines.map((line) => (Array.isArray(line?.path) ? line.path.length : 0)),
  );
  const distinctRuleIds = [...new Set(canonicalRuleIds)];
  const derivedRuleIds = distinctRuleIds.filter(
    (id) => RULE_KIND_BY_ID.get(id) === "derived",
  );
  return {
    lineCount: lines.length,
    subproofs,
    multiSubproofRules: canonicalRuleIds.filter((id) =>
      multiSubproofRules.has(id),
    ).length,
    maxDepth,
    extraDepth: Math.max(0, maxDepth - 1),
    distinctRuleIds,
    extraDistinctRules: Math.max(0, distinctRuleIds.length - 1),
    derivedRuleIds,
  };
}

export function scorePlanMetrics(
  metrics,
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  const weights = policy.score.weights;
  const factors = [
    [weights.linesAfterFirst, Math.max(0, metrics.lineCount - 1)],
    [weights.subproofs, metrics.subproofs],
    [weights.multiSubproofRules, metrics.multiSubproofRules],
    [weights.extraDepth, metrics.extraDepth],
    [weights.extraDistinctRules, metrics.extraDistinctRules],
  ];
  let total = 0;
  for (const [weight, amount] of factors) {
    if (weight === 0 || amount === 0) continue;
    if (weight > Number.MAX_VALUE / amount) return Number.MAX_VALUE;
    const contribution = weight * amount;
    if (total > Number.MAX_VALUE - contribution) return Number.MAX_VALUE;
    total += contribution;
  }
  return total;
}

export function trivialityScore(
  planningCost,
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  const cost = finiteNonnegative(planningCost, "planningCost");
  const scale = policy.score.normalizationScale;
  return Math.round(100 / (1 + cost / scale));
}

export function classifyDifficulty(
  metrics,
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  const planningCost = scorePlanMetrics(metrics, policy);
  const band =
    metrics.lineCount === 1
      ? "direct"
      : planningCost <= policy.thresholds.lightMaxInclusive
        ? "light"
        : "substantial";
  return {
    band,
    planningCost,
    trivialityScore: trivialityScore(planningCost, policy),
  };
}

export function selectDifficultyBand(
  randomValue,
  policy = DEFAULT_CHALLENGE_POLICY,
) {
  const value = Number(randomValue);
  if (!Number.isFinite(value) || value < 0 || value >= 1) {
    throw new RangeError("随机数必须位于 [0, 1) 内");
  }
  let cursor = value;
  for (const band of DIFFICULTY_BANDS) {
    cursor -= policy.bandWeights[band];
    if (cursor < 0) return band;
  }
  return [...DIFFICULTY_BANDS]
    .reverse()
    .find((band) => policy.bandWeights[band] > 0);
}
