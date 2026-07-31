export const FORM_META = Object.freeze({
  A: { name: "全称肯定", pattern: "所有 S 都是 P" },
  E: { name: "全称否定", pattern: "没有 S 是 P" },
  I: { name: "特称肯定", pattern: "有些 S 是 P" },
  O: { name: "特称否定", pattern: "有些 S 不是 P" },
});

const NEGATION = Object.freeze({ A: "O", E: "I", I: "E", O: "A" });

const LETTER_TERMS = Object.freeze(["S", "M", "P", "Q", "R"]);

const NATURAL_PATTERNS = Object.freeze({
  A: [
    (subject, predicate) => `所有${subject}都是${predicate}`,
    (subject, predicate) => `凡是${subject}，都是${predicate}`,
    (subject, predicate) => `${subject}无一例外都是${predicate}`,
    (subject, predicate) => `只有${predicate}才是${subject}`,
    (subject, predicate) => `${subject}全都属于${predicate}`,
  ],
  E: [
    (subject, predicate) => `没有${subject}是${predicate}`,
    (subject, predicate) => `凡是${subject}，都不是${predicate}`,
    (subject, predicate) => `${subject}没有一个是${predicate}`,
    (subject, predicate) => `不存在既是${subject}又是${predicate}的对象`,
    (subject, predicate) => `${subject}与${predicate}没有任何重合`,
  ],
  I: [
    (subject, predicate) => `有些${subject}是${predicate}`,
    (subject, predicate) => `至少有一个${subject}是${predicate}`,
    (subject, predicate) => `存在既是${subject}又是${predicate}的对象`,
    (subject, predicate) => `并非所有${subject}都不是${predicate}`,
    (subject, predicate) => `有的${subject}也属于${predicate}`,
  ],
  O: [
    (subject, predicate) => `有些${subject}不是${predicate}`,
    (subject, predicate) => `至少有一个${subject}不是${predicate}`,
    (subject, predicate) => `存在是${subject}但不是${predicate}的对象`,
    (subject, predicate) => `并非所有${subject}都是${predicate}`,
    (subject, predicate) => `不是每个${subject}都是${predicate}`,
  ],
});

const TERM_SETS = Object.freeze([
  ["诗人", "医生", "画家", "园丁", "钟表匠"],
  ["天文学家", "语言学家", "建筑师", "航海家", "植物学家"],
  ["棋手", "记者", "雕塑家", "程序员", "飞行员"],
  ["教师", "译者", "音乐家", "律师", "考古学家"],
  ["编辑", "摄影师", "木匠", "地理学家", "剧作家"],
  ["博物馆员", "工程师", "舞者", "数学家", "收藏家"],
]);

const s = (form, subject, predicate) => ({ form, subject, predicate });

export const CHALLENGE_TEMPLATES = Object.freeze([
  [s("A", 0, 1), s("A", 1, 2)],
  [s("A", 0, 1), s("E", 1, 2)],
  [s("I", 0, 1), s("A", 1, 2)],
  [s("I", 0, 1), s("E", 1, 2)],
  [s("A", 0, 1), s("A", 1, 2), s("A", 2, 3)],
  [s("I", 0, 1), s("A", 0, 2), s("A", 1, 3)],
  [s("A", 0, 1), s("A", 2, 3), s("E", 1, 3)],
  [s("O", 0, 1), s("A", 2, 1)],
  [s("A", 0, 1), s("O", 2, 1)],
  [s("O", 0, 1), s("A", 0, 2)],
  [s("I", 0, 1), s("A", 0, 2), s("A", 2, 3)],
  [s("E", 0, 1), s("A", 2, 0), s("A", 3, 1)],
  [s("I", 0, 1), s("A", 0, 2), s("A", 1, 3), s("A", 2, 4)],
  [s("A", 0, 1), s("A", 1, 2), s("A", 2, 3), s("A", 3, 4)],
  [s("I", 0, 1), s("A", 0, 2), s("A", 2, 3), s("E", 3, 4)],
  [s("A", 0, 1), s("E", 1, 2), s("A", 3, 0), s("I", 3, 4)],
]);

export function statementKey(statement) {
  return `${statement.form}:${statement.subject}:${statement.predicate}`;
}

export function negate(statement) {
  return { ...statement, form: NEGATION[statement.form] };
}

function formatStandardStatement(form, subject, predicate) {
  switch (form) {
    case "A":
      return `所有${subject}都是${predicate}`;
    case "E":
      return `没有${subject}是${predicate}`;
    case "I":
      return `有些${subject}是${predicate}`;
    case "O":
      return `有些${subject}不是${predicate}`;
    default:
      throw new Error(`未知的命题类型：${form}`);
  }
}

export function formatStandardCategorical(
  statement,
  terms,
  { mode = "natural" } = {},
) {
  const displayTerms = mode === "letters" ? LETTER_TERMS : terms;
  return formatStandardStatement(
    statement.form,
    displayTerms[statement.subject],
    displayTerms[statement.predicate],
  );
}

export function formatStatement(statement, terms, { mode = "natural" } = {}) {
  if (mode === "letters") {
    return formatStandardCategorical(statement, terms, { mode });
  }

  const subject = terms[statement.subject];
  const predicate = terms[statement.predicate];
  const patterns = NATURAL_PATTERNS[statement.form];
  const variant = Math.abs(statement.wordingVariant ?? 0) % patterns.length;
  return patterns[variant](subject, predicate);
}

export function naturalVariantCount(form) {
  return NATURAL_PATTERNS[form].length;
}

function maskSatisfiesUniversal(mask, statement) {
  const hasSubject = (mask & (1 << statement.subject)) !== 0;
  const hasPredicate = (mask & (1 << statement.predicate)) !== 0;

  if (statement.form === "A") return !hasSubject || hasPredicate;
  if (statement.form === "E") return !hasSubject || !hasPredicate;
  return true;
}

function maskWitnessesExistential(mask, statement) {
  const hasSubject = (mask & (1 << statement.subject)) !== 0;
  const hasPredicate = (mask & (1 << statement.predicate)) !== 0;

  if (statement.form === "I") return hasSubject && hasPredicate;
  if (statement.form === "O") return hasSubject && !hasPredicate;
  return true;
}

/**
 * Checks satisfiability for monadic categorical statements.
 *
 * Each bit mask is a possible unary type. A/E statements exclude types;
 * every I/O statement must retain at least one possible witness. Different
 * existential statements may use different witnesses, exactly as in FOL.
 */
export function isSatisfiable(statements, termCount) {
  const universals = statements.filter(({ form }) => form === "A" || form === "E");
  const existentials = statements.filter(({ form }) => form === "I" || form === "O");
  const allowedTypes = [];

  for (let mask = 0; mask < 2 ** termCount; mask += 1) {
    if (universals.every((statement) => maskSatisfiesUniversal(mask, statement))) {
      allowedTypes.push(mask);
    }
  }

  return existentials.every((statement) =>
    allowedTypes.some((mask) => maskWitnessesExistential(mask, statement)),
  );
}

export function entails(premises, conclusion, termCount) {
  return !isSatisfiable([...premises, negate(conclusion)], termCount);
}

function shuffled(items, random) {
  const copy = [...items];
  for (let index = copy.length - 1; index > 0; index -= 1) {
    const swapIndex = Math.floor(random() * (index + 1));
    [copy[index], copy[swapIndex]] = [copy[swapIndex], copy[index]];
  }
  return copy;
}

function allCandidateStatements(termCount) {
  const candidates = [];
  for (const form of Object.keys(FORM_META)) {
    for (let subject = 0; subject < termCount; subject += 1) {
      for (let predicate = 0; predicate < termCount; predicate += 1) {
        if (subject !== predicate) candidates.push(s(form, subject, predicate));
      }
    }
  }
  return candidates;
}

function chooseTermSet(random) {
  const source = TERM_SETS[Math.floor(random() * TERM_SETS.length)];
  return shuffled(source, random);
}

function difficultyFor(premises) {
  if (premises.length <= 2) return "基础";
  if (premises.length === 3) return "进阶";
  return "挑战";
}

export function generateChallenge(
  random = Math.random,
  previousSignature = "",
  requiredFollows = null,
) {
  if (requiredFollows !== null && typeof requiredFollows !== "boolean") {
    throw new TypeError("requiredFollows 必须是布尔值或 null。");
  }

  for (let attempt = 0; attempt < 120; attempt += 1) {
    const premises = CHALLENGE_TEMPLATES[
      Math.floor(random() * CHALLENGE_TEMPLATES.length)
    ].map((item) => ({
      ...item,
      wordingVariant: Math.floor(random() * naturalVariantCount(item.form)),
    }));
    const terms = chooseTermSet(random);
    const termCount = Math.max(
      ...premises.flatMap(({ subject, predicate }) => [subject, predicate]),
    ) + 1;
    const premiseKeys = new Set(premises.map(statementKey));
    const candidates = allCandidateStatements(termCount).filter(
      (candidate) => !premiseKeys.has(statementKey(candidate)),
    );
    const follows = requiredFollows ?? random() >= 0.5;
    const source = shuffled(
      candidates.filter(
        (candidate) => entails(premises, candidate, termCount) === follows,
      ),
      random,
    );
    if (source.length === 0) continue;

    const conclusion = {
      ...source[0],
      wordingVariant: Math.floor(random() * naturalVariantCount(source[0].form)),
    };
    const signature = `${premises.map(statementKey).join("|")}::${statementKey(
      conclusion,
    )}::${terms.slice(0, termCount).join("|")}`;

    if (signature === previousSignature) continue;

    return {
      id: `${Date.now()}-${Math.floor(random() * 1_000_000)}`,
      signature,
      terms: terms.slice(0, termCount),
      premises,
      conclusion,
      follows,
      difficulty: difficultyFor(premises),
    };
  }

  throw new Error("暂时无法生成新题，请重试。");
}
