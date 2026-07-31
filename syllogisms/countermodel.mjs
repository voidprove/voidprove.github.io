import {
  formatStandardCategorical,
  negate,
} from "./logic.mjs?v=20260731";

const OBJECT_NAMES = Object.freeze(["甲", "乙", "丙", "丁", "戊"]);

function maskSatisfiesUniversal(mask, item) {
  const hasSubject = (mask & (1 << item.subject)) !== 0;
  const hasPredicate = (mask & (1 << item.predicate)) !== 0;

  if (item.form === "A") return !hasSubject || hasPredicate;
  if (item.form === "E") return !hasSubject || !hasPredicate;
  return true;
}

function maskWitnessesExistential(mask, item) {
  const hasSubject = (mask & (1 << item.subject)) !== 0;
  const hasPredicate = (mask & (1 << item.predicate)) !== 0;

  if (item.form === "I") return hasSubject && hasPredicate;
  if (item.form === "O") return hasSubject && !hasPredicate;
  return false;
}

function populationCount(value) {
  let remaining = value;
  let count = 0;
  while (remaining > 0) {
    count += remaining & 1;
    remaining >>>= 1;
  }
  return count;
}

function compareModels(left, right) {
  if (!right) return -1;
  if (left.masks.length !== right.masks.length) {
    return left.masks.length - right.masks.length;
  }
  if (left.memberships !== right.memberships) {
    return left.memberships - right.memberships;
  }
  for (let index = 0; index < left.masks.length; index += 1) {
    if (left.masks[index] !== right.masks[index]) {
      return left.masks[index] - right.masks[index];
    }
  }
  return 0;
}

export function holdsInModel(item, masks) {
  if (item.form === "A" || item.form === "E") {
    return masks.every((mask) => maskSatisfiesUniversal(mask, item));
  }
  return masks.some((mask) => maskWitnessesExistential(mask, item));
}

export function findCountermodel(premises, conclusion, termCount) {
  const augmented = [...premises, negate(conclusion)];
  const universals = augmented.filter(
    ({ form }) => form === "A" || form === "E",
  );
  const existentials = augmented.filter(
    ({ form }) => form === "I" || form === "O",
  );
  const allowedMasks = [];

  for (let mask = 0; mask < 2 ** termCount; mask += 1) {
    if (universals.every((item) => maskSatisfiesUniversal(mask, item))) {
      allowedMasks.push(mask);
    }
  }

  if (existentials.length === 0) {
    return { masks: [0], termCount };
  }

  const fullCoverage = (1 << existentials.length) - 1;
  let states = new Map([[0, { masks: [], memberships: 0 }]]);

  for (const mask of allowedMasks) {
    let coverage = 0;
    existentials.forEach((item, index) => {
      if (maskWitnessesExistential(mask, item)) coverage |= 1 << index;
    });
    if (coverage === 0) continue;

    const next = new Map(states);
    for (const [covered, model] of states) {
      const combinedCoverage = covered | coverage;
      const candidate = {
        masks: [...model.masks, mask].sort((left, right) => left - right),
        memberships: model.memberships + populationCount(mask),
      };
      if (compareModels(candidate, next.get(combinedCoverage)) < 0) {
        next.set(combinedCoverage, candidate);
      }
    }
    states = next;
  }

  const result = states.get(fullCoverage);
  if (!result) return null;
  return { masks: result.masks, termCount };
}

function referenceNames(masks, predicate) {
  return masks
    .map((mask, index) => (predicate(mask) ? OBJECT_NAMES[index] : null))
    .filter(Boolean);
}

function listNames(names) {
  return names.join("、");
}

function reasonFor(item, masks, terms, truth) {
  const subject = terms[item.subject];
  const predicate = terms[item.predicate];
  const subjectMembers = referenceNames(
    masks,
    (mask) => (mask & (1 << item.subject)) !== 0,
  );
  const overlap = referenceNames(
    masks,
    (mask) =>
      (mask & (1 << item.subject)) !== 0 &&
      (mask & (1 << item.predicate)) !== 0,
  );
  const counterexamples = referenceNames(
    masks,
    (mask) =>
      (mask & (1 << item.subject)) !== 0 &&
      (mask & (1 << item.predicate)) === 0,
  );

  if (item.form === "A") {
    if (!truth) {
      return `${counterexamples[0]}是${subject}，但不是${predicate}。`;
    }
    if (subjectMembers.length === 0) {
      return `模型中没有${subject}，所以不存在反例。`;
    }
    return `${subject}的成员(${listNames(subjectMembers)})也都是${predicate}。`;
  }

  if (item.form === "E") {
    return truth
      ? `没有对象同时是${subject}和${predicate}。`
      : `${overlap[0]}同时是${subject}和${predicate}。`;
  }

  if (item.form === "I") {
    return truth
      ? `${overlap[0]}同时是${subject}和${predicate}。`
      : `没有对象同时是${subject}和${predicate}。`;
  }

  if (truth) {
    return `${counterexamples[0]}是${subject}，但不是${predicate}。`;
  }
  if (subjectMembers.length === 0) {
    return `模型中没有${subject}，所以不存在所需的见证。`;
  }
  return `模型中的每个${subject}也都是${predicate}。`;
}

export function describeCountermodel(model, premises, conclusion, terms) {
  if (!model) return null;

  const objects = model.masks.map((mask, index) => {
    const positive = terms.filter(
      (_, termIndex) => (mask & (1 << termIndex)) !== 0,
    );
    const negative = terms.filter(
      (_, termIndex) => (mask & (1 << termIndex)) === 0,
    );
    let description = "";

    if (positive.length === 0) {
      description = "不属于上述任何类别。";
    } else if (negative.length === 0) {
      description = `是${listNames(positive)}。`;
    } else {
      description = `是${listNames(positive)}；不是${listNames(negative)}。`;
    }

    return {
      name: OBJECT_NAMES[index],
      mask,
      positive,
      negative,
      description,
    };
  });

  const extensions = terms.map((term, termIndex) => ({
    term,
    members: referenceNames(
      model.masks,
      (mask) => (mask & (1 << termIndex)) !== 0,
    ),
  }));

  const checks = premises.map((item, index) => ({
    kind: "premise",
    index: index + 1,
    statement: { ...item },
    statementText: formatStandardCategorical(item, terms),
    truth: true,
    reason: reasonFor(item, model.masks, terms, true),
  }));

  checks.push({
    kind: "conclusion",
    statement: { ...conclusion },
    statementText: formatStandardCategorical(conclusion, terms),
    truth: false,
    reason: reasonFor(conclusion, model.masks, terms, false),
  });

  return {
    domain: objects.map(({ name }) => name),
    objects,
    extensions,
    checks,
  };
}

export function verifyCountermodel(model, premises, conclusion) {
  return Boolean(
    model?.masks?.length > 0 &&
      premises.every((item) => holdsInModel(item, model.masks)) &&
      !holdsInModel(conclusion, model.masks),
  );
}
