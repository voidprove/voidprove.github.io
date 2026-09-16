import { analyzePuzzle, enumeratePlacements } from './puzzle-quality.mjs';

// Finite Kripke semantics for normal modal logic K. Stacks read outside-in.
export const atom = name => ({ type: 'atom', name });
export const unary = child => ({ type: 'not', child });
export const binary = (type, left, right) => ({ type, left, right });
export function indexTree(tree) {
  let next = 0;
  function visit(n) { n.id = next++; if (n.child) visit(n.child); if (n.left) { visit(n.left); visit(n.right); } }
  visit(tree); return tree;
}
export function nodes(tree) { return [tree, ...(tree.child ? nodes(tree.child) : tree.left ? [...nodes(tree.left), ...nodes(tree.right)] : [])]; }
export function evaluate(model, tree, placement = {}, world = model.actual) {
  const successors = model.edges.filter(e => e[0] === world).map(e => e[1]);
  function at(n, w, depth = 0) {
    const stack = placement[n.id] || [];
    if (depth < stack.length) {
      const accessible = w === world ? successors : model.edges.filter(e => e[0] === w).map(e => e[1]);
      if (stack[depth] === 'box') return accessible.every(v => at(n, v, depth + 1));
      if (stack[depth] === 'diamond') return accessible.some(v => at(n, v, depth + 1));
      throw new Error('Unknown modal operator');
    }
    switch (n.type) {
      case 'atom': return model.worlds[w].atoms.includes(n.name);
      case 'not': return !at(n.child, w);
      case 'and': return at(n.left, w) && at(n.right, w);
      case 'or': return at(n.left, w) || at(n.right, w);
      case 'implies': return !at(n.left, w) || at(n.right, w);
      default: throw new Error('Unknown formula node');
    }
  }
  return at(tree, world);
}
export function format(tree, placement = {}, labels = false) {
  const pre = (placement[tree.id] || []).map(x => x === 'box' ? '□' : '◇').join('');
  const mark = labels ? `[${tree.id + 1}]` : '';
  const body = tree.type === 'atom' ? tree.name : tree.type === 'not' ? `¬${format(tree.child, placement, labels)}` : `(${format(tree.left, placement, labels)} ${{and:'∧',or:'∨',implies:'→'}[tree.type]} ${format(tree.right, placement, labels)})`;
  return mark + pre + body;
}
export function validInventory(placement, inventory) {
  const used = Object.values(placement).flat();
  return used.every(x => x === 'diamond' || x === 'box') && ['diamond', 'box'].every(x => used.filter(y => y === x).length === inventory[x]);
}
export function check(puzzle, placement) {
  const ids = new Set(nodes(puzzle.formula).map(n => String(n.id)));
  return Object.keys(placement).every(id => ids.has(id)) && validInventory(placement, puzzle.inventory) && evaluate(puzzle.model, puzzle.formula, placement);
}
export function random(seed) {
  let a = seed >>> 0;
  return () => { a += 0x6D2B79F5; let t = a; t = Math.imul(t ^ t >>> 15, t | 1); t ^= t + Math.imul(t ^ t >>> 7, t | 61); return ((t ^ t >>> 14) >>> 0) / 4294967296; };
}
const templates = [
  () => binary('and', atom('p'), atom('q')),
  () => unary(atom('p')),
  () => binary('implies', atom('p'), atom('q')),
  () => binary('or', atom('p'), atom('q')),
  () => unary(binary('and', atom('p'), atom('q'))),
  () => binary('and', binary('implies', atom('p'), atom('q')), atom('p')),
  () => binary('or', binary('and', atom('p'), atom('q')), atom('r')),
];
// Audited serial models, each with exactly one solution for its inventory.
// Used only when the bounded random search cannot meet the quality limits.
const fallbackModels = {
  2: {worlds:[{atoms:[]},{atoms:['p']},{atoms:['p','q','r']},{atoms:['q','r']}],edges:[[0,0],[0,1],[0,3],[1,3],[2,0],[2,1],[3,0],[3,1]],actual:0},
  3: {worlds:[{atoms:[]},{atoms:['q']},{atoms:['p','q','r']},{atoms:['p','r']},{atoms:['r']}],edges:[[0,0],[0,2],[4,0],[4,1],[1,0],[2,4],[3,1]],actual:0},
  4: {worlds:[{atoms:['r']},{atoms:['p','r']},{atoms:['q','r']},{atoms:['r']},{atoms:['p']},{atoms:['p','q','r']}],edges:[[0,3],[1,3],[1,5],[2,5],[3,1],[3,4],[4,3],[5,3]],actual:0},
};
export const GENERATION_LIMITS = Object.freeze({maxSolutions:3, maxSolutionRate:0.15, maxVacuousSolutions:0, maxAttempts:350});
export function generatePuzzle(level, seed, {maxAttempts = GENERATION_LIMITS.maxAttempts} = {}) {
  if (!Number.isSafeInteger(level) || level < 1) throw new Error('Level must be a positive integer');
  if (!Number.isInteger(maxAttempts) || maxAttempts < 0 || maxAttempts > GENERATION_LIMITS.maxAttempts) throw new Error('Invalid generation attempt limit');
  const rng = random((seed ^ Math.imul(level, 2654435761)) >>> 0);
  const pick = a => a[Math.floor(rng() * a.length)];
  const count = level <= 2 ? 1 : level <= 5 ? 2 : level <= 9 ? 3 : 4;
  const inventory = level === 1 ? {diamond:1,box:0} : level === 2 ? {diamond:0,box:1} : {diamond:Math.ceil(count / 2),box:Math.floor(count / 2)};
  const tokens = [...Array(inventory.diamond).fill('diamond'), ...Array(inventory.box).fill('box')];
  if (level <= 2) {
    const worlds = Array.from({length:3}, (_, i) => ({atoms:i === 0 ? [] : level === 2 || i === 1 ? ['p'] : []}));
    if (level === 1 && rng() < .5) [worlds[1], worlds[2]] = [worlds[2], worlds[1]];
    return {level, seed, inventory, formula:indexTree(atom('p')), model:{worlds,edges:[[0,1],[0,2]],actual:0}, witness:{0:[tokens[0]]}};
  }
  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    const formula = indexTree(templates[Math.floor(rng() * (level < 6 ? 4 : templates.length))]());
    const size = Math.min(6, 3 + Math.floor(level / 3));
    const worlds = Array.from({length:size}, () => ({atoms:['p','q','r'].filter(() => rng() < .48)}));
    const edges = [];
    for (let a = 0; a < size; a++) for (let b = 0; b < size; b++) if (rng() < (a === b ? .10 : .30)) edges.push([a,b]);
    if (!edges.some(e => e[0] === 0)) edges.push([0, 1]);
    // Usually give terminal worlds a successor, but retain some dead ends.
    // Exact quality checks below decide whether they make a puzzle too easy.
    for (let w = 0; w < size; w++) if (!edges.some(e => e[0] === w) && rng() < .8) edges.push([w, pick(Array.from({length:size}, (_,i) => i).filter(i => i !== w))]);
    const model = {worlds, edges, actual:0};
    if (evaluate(model, formula)) continue;
    const maxSolutions = Math.min(GENERATION_LIMITS.maxSolutions, Math.floor(enumeratePlacements(formula, inventory).length * GENERATION_LIMITS.maxSolutionRate));
    if (!maxSolutions) continue;
    const candidate = {level, seed, inventory, formula, model};
    const quality = analyzePuzzle(candidate, {maxSolutions, maxVacuousSolutions:GENERATION_LIMITS.maxVacuousSolutions});
    if (quality.exhaustive && quality.solutionCount > 0) return {...candidate, witness:quality.witness, quality};
  }
  const fallback = {level, seed, inventory, formula:indexTree(binary('and',atom('p'),atom('q'))), model:structuredClone(fallbackModels[count])};
  const quality = analyzePuzzle(fallback);
  return {...fallback, witness:quality.witness, quality};
}
