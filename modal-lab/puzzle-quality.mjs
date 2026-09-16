// Count syntactically distinct placements, treating identical tokens alike.
const placementCache = new Map();
export function enumeratePlacements(formula, inventory) {
  const ids = [];
  function visit(n) { ids.push(n.id); if (n.child) visit(n.child); if (n.left) { visit(n.left); visit(n.right); } }
  visit(formula);
  const key = `${ids.join(',')}/${inventory.diamond}/${inventory.box}`;
  if (placementCache.has(key)) return placementCache.get(key);
  const results = [], placement = {};
  function slot(i, diamonds, boxes) {
    if (i === ids.length) {
      if (!diamonds && !boxes) results.push(Object.freeze(Object.fromEntries(Object.entries(placement).map(([id,ops]) => [id,Object.freeze([...ops])]))));
      return;
    }
    const word = [];
    function extend(d, b) {
      if (word.length) placement[ids[i]] = word;
      else delete placement[ids[i]];
      slot(i + 1, d, b);
      if (d) { word.push('diamond'); extend(d - 1, b); word.pop(); }
      if (b) { word.push('box'); extend(d, b - 1); word.pop(); }
    }
    extend(diamonds, boxes);
    delete placement[ids[i]];
  }
  slot(0, inventory.diamond, inventory.box);
  Object.freeze(results);
  placementCache.set(key, results);
  return results;
}

// Besides ordinary K truth, compute conservative truth/falsity certificates
// that never use a modal fact at a dead end. At a terminal box or diamond,
// both certificates are absent. Treating a terminal diamond symmetrically
// also catches the equivalent shortcut through negated diamonds. Negation
// swaps certificates without changing the ordinary game semantics.
export function analyzePuzzle({model, formula, inventory}, limits = {}) {
  if (model.worlds.length > 30) throw new Error('Quality analysis supports at most 30 worlds');
  const placements = enumeratePlacements(formula, inventory);
  const all = (1 << model.worlds.length) - 1;
  const outgoing = model.worlds.map((_,w) => model.edges.reduce((mask,[a,b]) => a === w ? mask | (1 << b) : mask, 0));
  const atomMasks = {};
  for (const w of model.worlds) for (const name of w.atoms) {
    atomMasks[name] ??= model.worlds.reduce((mask,v,i) => v.atoms.includes(name) ? mask | (1 << i) : mask, 0);
  }
  function denotation(n, placement) {
    let truth, yes, no;
    if (n.type === 'atom') { truth = atomMasks[n.name] || 0; yes = truth; no = all ^ truth; }
    else if (n.type === 'not') { const c = denotation(n.child, placement); truth = all ^ c[0]; yes = c[2]; no = c[1]; }
    else {
      const l = denotation(n.left, placement), r = denotation(n.right, placement);
      if (n.type === 'and') { truth = l[0] & r[0]; yes = l[1] & r[1]; no = l[2] | r[2]; }
      else if (n.type === 'or') { truth = l[0] | r[0]; yes = l[1] | r[1]; no = l[2] & r[2]; }
      else if (n.type === 'implies') { truth = (all ^ l[0]) | r[0]; yes = l[2] | r[1]; no = l[1] & r[2]; }
      else throw new Error('Unknown formula node');
    }
    const stack = placement[n.id] || [];
    for (let i = stack.length - 1; i >= 0; i--) {
      let t = 0, y = 0, f = 0;
      for (let w = 0; w < outgoing.length; w++) {
        const next = outgoing[w], bit = 1 << w;
        if (stack[i] === 'box') {
          if ((next & truth) === next) t |= bit;
          if (next && (next & yes) === next) y |= bit;
          if (next & no) f |= bit;
        } else {
          if (next & truth) t |= bit;
          if (next & yes) y |= bit;
          if (next && (next & no) === next) f |= bit;
        }
      }
      truth = t; yes = y; no = f;
    }
    return [truth, yes, no];
  }
  const result = {placementCount:placements.length, solutionCount:0, robustSolutionCount:0, vacuousSolutionCount:0, witness:null, exhaustive:true};
  const actual = 1 << model.actual;
  for (const placement of placements) {
    const [truth, yes] = denotation(formula, placement);
    if (!(truth & actual)) continue;
    result.solutionCount++;
    if (yes & actual) { result.robustSolutionCount++; result.witness ??= placement; }
    else result.vacuousSolutionCount++;
    if (result.solutionCount > (limits.maxSolutions ?? Infinity) || result.vacuousSolutionCount > (limits.maxVacuousSolutions ?? Infinity)) {
      result.exhaustive = false;
      break;
    }
  }
  result.solutionRate = result.solutionCount / result.placementCount;
  return result;
}
