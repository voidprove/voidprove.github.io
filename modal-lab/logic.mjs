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
export function generatePuzzle(level, seed) {
  if (!Number.isSafeInteger(level) || level < 1) throw new Error('Level must be a positive integer');
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
  for (let attempt = 0; attempt < 350; attempt++) {
    const formula = indexTree(templates[Math.floor(rng() * (level < 6 ? 4 : templates.length))]());
    const size = Math.min(6, 3 + Math.floor(level / 3));
    const worlds = Array.from({length:size}, () => ({atoms:['p','q','r'].filter(() => rng() < .48)}));
    const edges = [];
    for (let a = 0; a < size; a++) for (let b = 0; b < size; b++) if (rng() < (a === b ? .10 : .30)) edges.push([a,b]);
    if (!edges.some(e => e[0] === 0)) edges.push([0, 1]);
    const model = {worlds, edges, actual:0};
    if (evaluate(model, formula)) continue;
    const slots = nodes(formula).map(n => n.id);
    let witness = null, rejected = false;
    for (let sample = 0; sample < 80; sample++) {
      const placement = {};
      const shuffled = [...tokens];
      for (let i = shuffled.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [shuffled[i],shuffled[j]] = [shuffled[j],shuffled[i]]; }
      for (const token of shuffled) (placement[pick(slots)] ??= []).push(token);
      if (evaluate(model, formula, placement)) witness ??= placement; else rejected = true;
      if (witness && rejected) return {level, seed, inventory, formula, model, witness};
    }
  }
  // A constructive fallback: any nonempty modal string takes false p at w0
  // to true p at a reflexive successor. The inventory is preserved exactly.
  return {level, seed, inventory, formula:indexTree(binary('and',atom('p'),atom('q'))), model:{worlds:[{atoms:['q']},{atoms:['p','q']}],edges:[[0,1],[1,1]],actual:0}, witness:{1:tokens}};
}
