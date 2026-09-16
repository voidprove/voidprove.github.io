import assert from 'node:assert/strict';
import {atom, unary, binary, indexTree, nodes, evaluate, check, generatePuzzle, GENERATION_LIMITS} from '../modal-lab/logic.mjs';
import {enumeratePlacements, analyzePuzzle} from '../modal-lab/puzzle-quality.mjs';

// Independent recursive three-valued oracle. A terminal modality is unknown
// (0), not false. This catches negative scopes and avoids treating an irrelevant
// vacuous branch of a disjunction as a dependency.
function certificate(model, formula, placement, world = model.actual) {
  function at(n,w,depth=0) {
    const stack=placement[n.id] || [];
    if(depth<stack.length) {
      const next=model.edges.filter(([a])=>a===w).map(([,b])=>b);
      const values=next.map(v=>at(n,v,depth+1));
      if(stack[depth]==='box') return values.length ? Math.min(...values) : 0;
      return values.length ? Math.max(...values) : 0;
    }
    if(n.type==='atom') return model.worlds[w].atoms.includes(n.name)?1:-1;
    if(n.type==='not') return -at(n.child,w);
    const l=at(n.left,w),r=at(n.right,w);
    return n.type==='and'?Math.min(l,r):n.type==='or'?Math.max(l,r):Math.max(-l,r);
  }
  return at(formula,world);
}
function choose(n,k) {let c=1;for(let i=1;i<=k;i++)c=c*(n-i+1)/i;return Math.round(c);}
for(let depth=0;depth<5;depth++) for(const inventory of [{diamond:1,box:1},{diamond:2,box:1},{diamond:2,box:2}]) {
  let tree=atom('p');for(let i=0;i<depth;i++)tree=unary(tree);indexTree(tree);
  const ps=enumeratePlacements(tree,inventory),n=nodes(tree).length,k=inventory.diamond+inventory.box;
  // Weak compositions of k across n slots, times distinct operator words.
  assert.equal(ps.length,choose(k+n-1,n-1)*choose(k,inventory.diamond));
  assert.equal(new Set(ps.map(p=>JSON.stringify(p))).size,ps.length);
  for(const p of ps) {
    const used=Object.values(p).flat();
    assert.equal(used.filter(x=>x==='diamond').length,inventory.diamond);
    assert.equal(used.filter(x=>x==='box').length,inventory.box);
  }
}
const dead={worlds:[{atoms:[]}],edges:[],actual:0};
const boxOnly={diamond:0,box:1};
const vacuous={model:dead,formula:indexTree(atom('p')),inventory:boxOnly};
assert.equal(check(vacuous,{0:['box']}),true,'the game still uses normal K semantics');
assert.equal(analyzePuzzle(vacuous).vacuousSolutionCount,1);
const dualShortcut={model:dead,formula:indexTree(unary(atom('p'))),inventory:{diamond:1,box:0}};
assert.equal(analyzePuzzle(dualShortcut).solutionCount,1);
assert.equal(analyzePuzzle(dualShortcut).robustSolutionCount,0,'not diamond p must not bypass the penalty on box not p');
const irrelevant={model:{...dead,worlds:[{atoms:['q']}]},formula:indexTree(binary('or',atom('q'),atom('p'))),inventory:boxOnly};
assert.equal(analyzePuzzle(irrelevant).solutionCount,3);
assert.equal(analyzePuzzle(irrelevant).robustSolutionCount,1,'q or box p has a non-vacuous truth certificate');
const antecedent={model:dead,formula:indexTree(binary('implies',atom('p'),atom('q'))),inventory:boxOnly};
assert.equal(analyzePuzzle(antecedent).robustSolutionCount,1,'a false antecedent can make the vacuous consequent irrelevant');
const cancellation={model:dead,formula:indexTree(binary('or',atom('p'),unary(atom('q')))),inventory:{diamond:0,box:2}};
const cancelPlacement={1:['box'],3:['box']};
assert.equal(evaluate(dead,cancellation.formula,cancelPlacement),true);
assert.equal(certificate(dead,cancellation.formula,cancelPlacement),0,'flipping every empty box to false would miss this sensitivity');
for(const puzzle of [vacuous,dualShortcut,irrelevant,antecedent,cancellation]) {
  const ps=enumeratePlacements(puzzle.formula,puzzle.inventory);
  const solutions=ps.filter(p=>evaluate(puzzle.model,puzzle.formula,p));
  const robust=solutions.filter(p=>certificate(puzzle.model,puzzle.formula,p)===1);
  const a=analyzePuzzle(puzzle);
  assert.equal(a.solutionCount,solutions.length);
  assert.equal(a.robustSolutionCount,robust.length);
}
assert.equal(analyzePuzzle(irrelevant,{maxSolutions:1}).exhaustive,false,'early rejection must be marked incomplete');
assert.equal(analyzePuzzle(vacuous,{maxVacuousSolutions:0}).exhaustive,false);

for(const level of [3,6,10,40]) {
  const p=generatePuzzle(level,12,{maxAttempts:0});
  assert.equal(p.quality.solutionCount,1,'fallback must also be selective');
  assert.equal(p.quality.vacuousSolutionCount,0);
  assert.equal(certificate(p.model,p.formula,p.witness),1);
}

const stats={puzzles:0,solutions:0,vacuous:0,unique:0,maxSolutions:0,withDeadEnds:0,meanSolutionRate:0,maxGenerationMs:0};
for(let seed=0;seed<50;seed++)for(let level=3;level<=20;level++) {
  const start=performance.now(),p=generatePuzzle(level,seed);
  stats.maxGenerationMs=Math.max(stats.maxGenerationMs,performance.now()-start);
  const ps=enumeratePlacements(p.formula,p.inventory);
  const solutions=ps.filter(x=>evaluate(p.model,p.formula,x));
  const robust=solutions.filter(x=>certificate(p.model,p.formula,x)===1);
  assert(solutions.length>0 && solutions.length<=GENERATION_LIMITS.maxSolutions);
  assert(solutions.length/ps.length<=GENERATION_LIMITS.maxSolutionRate);
  assert.equal(robust.length,solutions.length,'every accepted placement must have a non-vacuous certificate');
  assert.equal(p.quality.solutionCount,solutions.length);
  assert.equal(p.quality.placementCount,ps.length);
  assert.equal(p.quality.vacuousSolutionCount,0);
  assert.equal(p.quality.exhaustive,true);
  assert.equal(evaluate(p.model,p.formula),false);
  assert.equal(check(p,p.witness),true);
  stats.puzzles++;stats.solutions+=solutions.length;stats.unique+=solutions.length===1;
  stats.maxSolutions=Math.max(stats.maxSolutions,solutions.length);
  stats.withDeadEnds+=p.model.worlds.some((_,w)=>!p.model.edges.some(([a])=>a===w));
  stats.meanSolutionRate+=solutions.length/ps.length;
}
stats.meanSolutionRate/=stats.puzzles;
console.log('Exact generation-quality audit passed:',JSON.stringify(stats));
