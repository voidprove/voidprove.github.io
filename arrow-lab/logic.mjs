const subscript = '₀₁₂₃₄₅₆₇₈₉';
export const worldLabel = world => `Γ${subscript[world + 1]}`;

export const rules = {
  any: { label: 'Unrestricted', description: 'Any arrows are allowed, including loops.' },
  reflexive: { label: 'Reflexive', description: 'Every world must have a loop to itself.' },
  symmetric: { label: 'Symmetric', description: 'Every arrow must have its reverse.' },
  serial: { label: 'Serial', description: 'Every world must have at least one outgoing arrow.' },
  transitive: { label: 'Transitive', description: 'Whenever two arrows form a path, the direct arrow must also be present.' },
  equivalence: { label: 'Equivalence', description: 'The arrows must be reflexive, symmetric, and transitive.' },
};

function world(atoms, ...requirements) {
  const usesR = atoms.includes('r') || requirements.some(formula => formula.includes('r'));
  const letters = usesR ? 'pqr' : 'pq';
  return {
    atoms,
    formulas: [...letters]
      .map(atom => atoms.includes(atom) ? atom : `¬${atom}`)
      .concat(requirements),
  };
}

export const levels = [
  {
    id: 'one-witness', title: 'A witness', rule: 'any', minimum: 1, layout: [0, 1, 2],
    description: 'A diamond needs at least one reachable world where its formula is true.',
    worlds: [world([], '◇p'), world(['p']), world(['q'])],
  },
  {
    id: 'split-witnesses', title: 'One of each', rule: 'any', minimum: 2, layout: [0, 1, 3, 2],
    description: 'The two diamonds need different witnesses. The box limits which worlds can supply them.',
    worlds: [
      world([], '□p', '◇q', '◇¬q'),
      world(['p', 'q']),
      world(['p']),
      world(['q']),
    ],
  },
  {
    id: 'two-steps', title: 'Two steps away', rule: 'any', minimum: 4, layout: [0, 1, 2, 3],
    description: 'Read nested diamonds one arrow at a time.',
    worlds: [
      world(['q'], '□¬q', '◇◇(p ∧ q)'),
      world([], '□q', '◇p'),
      world(['p', 'q'], '□¬p', '◇(¬p ∧ q)'),
      world(['p'], '□¬p', '◇(¬p ∧ q)'),
    ],
  },
  {
    id: 'worksheet-any', title: 'The five worlds', rule: 'any', minimum: 6, layout: [0, 1, 4, 3, 2],
    description: 'Every world reached from Γ₁ must itself have a successor where p is false.',
    worlds: [
      world(['p', 'q'], '□p', '◇q', '◇¬q', '□◇¬p'),
      world(['p', 'q'], '□¬q', '◇¬p'),
      world(['p'], '□¬p', '◇q'),
      world(['q'], '□¬p', '◇¬q'),
      world([], '□q', '◇p'),
    ],
  },
  {
    id: 'loops', title: 'Loop back', rule: 'reflexive', minimum: 5, layout: [0, 1, 2],
    description: 'A loop lets a world witness its own diamond if the formula holds there.',
    worlds: [
      world(['p'], '□p', '◇(p ∧ q)'),
      world(['p', 'q'], '◇¬p'),
      world(['q'], '□¬p', '◇q'),
    ],
  },
  {
    id: 'worksheet-reflexive', title: 'Looking back', rule: 'reflexive', minimum: 10, layout: [0, 1, 3, 4, 2],
    description: 'Every loop also counts toward its world’s box formulas.',
    worlds: [
      world(['p', 'q'], '□p', '◇□¬q'),
      world(['p', 'q'], '□q', '◇□¬p'),
      world(['p'], '□¬q', '◇¬p'),
      world(['q'], '□¬p', '◇¬q'),
      world([], '◇p'),
    ],
  },
  {
    id: 'return-trip', title: 'A return trip', rule: 'symmetric', minimum: 2, layout: [0, 1, 2],
    description: 'An arrow and its reverse have to satisfy the formulas at both ends.',
    worlds: [
      world(['p'], '□¬p', '◇q'),
      world(['q'], '□p', '◇p'),
      world(['p', 'q'], '□¬p'),
    ],
  },
  {
    id: 'worksheet-symmetric', title: 'Full circle', rule: 'symmetric', minimum: 10, layout: [0, 1, 2, 3, 4],
    description: 'Find a set of reciprocal arrows that meets every world’s demands.',
    worlds: [
      world(['p', 'q'], '□¬q', '◇p', '◇¬p'),
      world(['p'], '□q', '◇p', '◇¬p'),
      world(['q'], '□p', '◇q', '◇¬q'),
      world(['p', 'q'], '□¬p', '◇q', '◇¬q'),
      world([], '□(p ∧ q)', '◇□¬q', '◇□¬p'),
    ],
  },
  {
    id: 'serial', title: 'No dead ends', rule: 'serial', minimum: 4, layout: [0, 2, 3, 1],
    description: 'Since every world has a successor, □p and □¬p cannot both be true at one world.',
    worlds: [
      world([], '□q', '◇□p'),
      world(['p', 'q'], '□(¬p ∧ q)'),
      world(['q'], '◇(p ∧ ¬q)'),
      world(['p'], '□(p ∧ q)'),
    ],
  },
  {
    id: 'transitive', title: 'Take the shortcut', rule: 'transitive', minimum: 6, layout: [0, 1, 2, 3],
    description: 'After building a path, check all pairs of arrows that can be followed in sequence.',
    worlds: [
      world([], '◇(p ∧ ¬q)'),
      world(['p'], '□q', '◇(p ∧ q)'),
      world(['p', 'q'], '◇(¬p ∧ q)'),
      world(['q']),
    ],
  },
  {
    id: 'equivalence', title: 'Separate classes', rule: 'equivalence', minimum: 9, layout: [0, 1, 4, 2, 3],
    description: 'An equivalence relation splits the worlds into groups. Every world can reach all members of its own group.',
    worlds: [
      world(['p'], '□(p ∨ q)', '◇(p ∧ q)'),
      world(['p', 'q'], '□p'),
      world(['q'], '□¬p', '◇¬q'),
      world([], '◇q'),
      world(['p'], '□¬q'),
    ],
  },
  {
    id: 'mixed-scope', title: 'Follow the clues', rule: 'any', minimum: 6, layout: [0, 1, 2, 3, 4],
    description: 'Use the boxes to rule out arrows, then work out which of the remaining paths meet the nested requirement.',
    worlds: [
      world(['p', 'q'], '□(p → r)', '◇p', '◇¬p', '□◇q'),
      world(['p', 'r'], '□(r → q)', '◇(q ∧ ¬p)'),
      world(['q'], '□¬p', '◇r'),
      world(['r'], '□r', '◇q'),
      world(['p', 'q', 'r'], '□(q ∧ ¬r)', '◇p'),
    ],
  },
];

// Only the grammar used in authored puzzles: atoms, parentheses, unary
// operators, and Boolean connectives. Implication associates to the right.
function parseFormula(source) {
  const tokens = source.replace(/\s/gu, '');
  const precedence = { '→': 1, '∨': 2, '∧': 3 };
  let cursor = 0;

  function primary() {
    const op = tokens[cursor++];
    if (op === '(') {
      const node = expression();
      if (tokens[cursor++] !== ')') throw new SyntaxError(`Unclosed parenthesis in ${source}`);
      return node;
    }
    if (op === '¬' || op === '◇' || op === '□') {
      const child = primary();
      return { op, child, depth: child.depth + (op === '¬' ? 0 : 1) };
    }
    if (op === 'p' || op === 'q' || op === 'r') return { op, depth: 0 };
    throw new SyntaxError(`Invalid formula: ${source}`);
  }

  function expression(minimum = 1) {
    let left = primary();
    while ((precedence[tokens[cursor]] || 0) >= minimum) {
      const op = tokens[cursor++];
      const right = expression(precedence[op] + (op === '→' ? 0 : 1));
      left = { op, left, right, depth: Math.max(left.depth, right.depth) };
    }
    return left;
  }

  const tree = expression();
  if (cursor !== tokens.length) throw new SyntaxError(`Unexpected token in ${source}`);
  return tree;
}

// Each row stores a world's successors as a bitset. Formula evaluation
// returns a bitset of the worlds where the formula is true.
const bit = world => 1 << world;
const compiledLevels = new WeakMap();

function compile(puzzle) {
  if (!compiledLevels.has(puzzle)) {
    const atomMasks = { p: 0, q: 0, r: 0 };
    const formulas = puzzle.worlds.map(({ atoms, formulas }, index) => {
      for (const atom of atoms) atomMasks[atom] |= bit(index);
      return formulas.map(parseFormula);
    });
    compiledLevels.set(puzzle, {
      formulas,
      atomMasks,
      allWorlds: bit(puzzle.worlds.length) - 1,
    });
  }
  return compiledLevels.get(puzzle);
}

function truthSet(tree, rows, model) {
  const { op, child, left, right } = tree;
  switch (op) {
    case 'p': case 'q': case 'r': return model.atomMasks[op];
    case '¬': return model.allWorlds ^ truthSet(child, rows, model);
    case '∧': return truthSet(left, rows, model) & truthSet(right, rows, model);
    case '∨': return truthSet(left, rows, model) | truthSet(right, rows, model);
    case '→': return (model.allWorlds ^ truthSet(left, rows, model)) | truthSet(right, rows, model);
    case '◇': case '□': {
      const holds = truthSet(child, rows, model);
      let truth = 0;
      for (let world = 0; world < rows.length; world++) {
        const matching = rows[world] & holds;
        if (op === '◇' ? matching !== 0 : matching === rows[world]) truth |= bit(world);
      }
      return truth;
    }
  }
  throw new Error(`Unknown formula operator: ${op}`);
}

function frameViolations(rule, rows) {
  const violations = [];
  for (let from = 0; from < rows.length; from++) {
    if ((rule === 'reflexive' || rule === 'equivalence') && !(rows[from] & bit(from))) {
      violations.push(`${worldLabel(from)} needs a loop.`);
    }
    if (rule === 'serial' && rows[from] === 0) {
      violations.push(`${worldLabel(from)} needs an outgoing arrow.`);
    }
    for (let via = 0; via < rows.length; via++) {
      if (!(rows[from] & bit(via))) continue;
      if ((rule === 'symmetric' || rule === 'equivalence') && !(rows[via] & bit(from))) {
        violations.push(`${worldLabel(via)} → ${worldLabel(from)} is missing.`);
      }
      if (rule === 'transitive' || rule === 'equivalence') {
        const missing = rows[via] & ~rows[from];
        for (let to = 0; to < rows.length; to++) {
          if (missing & bit(to)) {
            violations.push(`${worldLabel(from)} → ${worldLabel(via)} → ${worldLabel(to)} requires ${worldLabel(from)} → ${worldLabel(to)}.`);
          }
        }
      }
    }
  }
  return violations;
}

function successorRows(puzzle, edges) {
  const rows = Array(puzzle.worlds.length).fill(0);
  for (const [from, to] of edges) {
    if (!Number.isInteger(from) || !Number.isInteger(to)
        || from < 0 || from >= rows.length || to < 0 || to >= rows.length) {
      throw new RangeError('An arrow must connect worlds in the puzzle');
    }
    rows[from] |= bit(to);
  }
  return rows;
}

export function evaluatePuzzle(puzzle, edges) {
  const rows = successorRows(puzzle, edges);
  const model = compile(puzzle);
  const worlds = model.formulas.map((formulas, world) =>
    formulas.map(formula => Boolean(truthSet(formula, rows, model) & bit(world))),
  );
  const frameIssues = frameViolations(puzzle.rule, rows);
  const frameOk = frameIssues.length === 0;
  return { solved: frameOk && worlds.every(formulas => formulas.every(Boolean)), worlds, frameOk, frameIssues };
}

function countBits(mask) {
  let total = 0;
  for (let remaining = mask; remaining; remaining &= remaining - 1) total++;
  return total;
}

const cachedSolutions = new WeakMap();

function minimumSolutions(puzzle) {
  if (cachedSolutions.has(puzzle)) return cachedSolutions.get(puzzle);
  const model = compile(puzzle);
  const rows = Array(puzzle.worlds.length).fill(0);

  // Only depth-one formulas can prune a row on its own. The solver checks
  // nested formulas and frame closure once all successor rows are known.
  const choices = model.formulas.map((formulas, from) => {
    const local = formulas.filter(formula => formula.depth <= 1);
    const candidates = [];
    for (let mask = 0; mask <= model.allWorlds; mask++) {
      if ((puzzle.rule === 'reflexive' || puzzle.rule === 'equivalence') && !(mask & bit(from))) continue;
      if (puzzle.rule === 'serial' && !mask) continue;
      rows[from] = mask;
      if (local.every(formula => truthSet(formula, rows, model) & bit(from))) {
        candidates.push({ mask, count: countBits(mask) });
      }
    }
    rows[from] = 0;
    return candidates.sort((first, second) => first.count - second.count);
  });
  const minimumTail = Array(rows.length + 1).fill(0);
  for (let from = rows.length - 1; from >= 0; from--) {
    minimumTail[from] = minimumTail[from + 1] + (choices[from][0]?.count ?? Infinity);
  }

  let best = Infinity;
  let solutions = [];
  function search(from, used) {
    if (from === rows.length) {
      if (frameViolations(puzzle.rule, rows).length) return;
      if (!model.formulas.every((formulas, world) => formulas.every(formula => truthSet(formula, rows, model) & bit(world)))) return;
      if (used < best) {
        best = used;
        solutions = [];
      }
      solutions.push([...rows]);
      return;
    }
    for (const { mask, count } of choices[from]) {
      if (used + count + minimumTail[from + 1] > best) break;
      rows[from] = mask;
      search(from + 1, used + count);
    }
  }
  search(0, 0);
  const result = { best, solutions };
  cachedSolutions.set(puzzle, result);
  return result;
}

export function analyzePuzzle(puzzle) {
  const { best, solutions } = minimumSolutions(puzzle);
  return { minimum: best, solutionCount: solutions.length };
}

export function findHint(puzzle, edges) {
  if (evaluatePuzzle(puzzle, edges).solved) return null;
  const current = successorRows(puzzle, edges);
  const { best, solutions } = minimumSolutions(puzzle);
  let target;
  let closest = Infinity;
  for (const solution of solutions) {
    const distance = solution.reduce((total, mask, world) => total + countBits(mask ^ current[world]), 0);
    if (distance < closest) {
      closest = distance;
      target = solution;
    }
  }
  if (!target) return null;

  let addition;
  let removal;
  for (let from = 0; from < current.length; from++) {
    for (let to = 0; to < current.length; to++) {
      const hasArrow = current[from] & bit(to);
      const needsArrow = target[from] & bit(to);
      if (!hasArrow && needsArrow) addition ??= { action: 'add', from, to };
      if (hasArrow && !needsArrow) removal ??= { action: 'remove', from, to };
    }
  }
  const used = current.reduce((total, mask) => total + countBits(mask), 0);
  return used < best ? addition ?? removal : removal ?? addition;
}
