import assert from 'node:assert/strict';
import { atom, unary, binary, indexTree, nodes, evaluate, generatePuzzle, check, format, validInventory } from '../modal-lab/logic.mjs';

// A separate denotation-based oracle evaluates sets of worlds bottom-up.
function truthSet(model, n, placement) {
  const all=model.worlds.map((_,i)=>i);
  let set;
  if(n.type==='atom') set=new Set(all.filter(i=>model.worlds[i].atoms.includes(n.name)));
  else if(n.type==='not') {const child=truthSet(model,n.child,placement);set=new Set(all.filter(i=>!child.has(i)));}
  else {
    const l=truthSet(model,n.left,placement),r=truthSet(model,n.right,placement);
    set=new Set(all.filter(i=>n.type==='and'?l.has(i)&&r.has(i):n.type==='or'?l.has(i)||r.has(i):!l.has(i)||r.has(i)));
  }
  for(const op of [...(placement[n.id]||[])].reverse()) {
    const previous=set;
    if(op==='diamond') set=new Set(model.edges.filter(([,b])=>previous.has(b)).map(([a])=>a));
    else {const bad=new Set(model.edges.filter(([,b])=>!previous.has(b)).map(([a])=>a));set=new Set(all.filter(i=>!bad.has(i)));}
  }
  return set;
}
const p=indexTree(atom('p'));
const dead={worlds:[{atoms:[]}],edges:[],actual:0};
assert.equal(evaluate(dead,p,{0:['box']}),true,'box vacuity');
assert.equal(evaluate(dead,p,{0:['diamond']}),false,'diamond at dead end');
const branching={worlds:[{atoms:[]},{atoms:['p']},{atoms:[]}],edges:[[0,1],[0,2],[1,1]],actual:0};
assert.equal(evaluate(branching,p,{0:['diamond']}),true);
assert.equal(evaluate(branching,p,{0:['box']}),false);
assert.equal(evaluate(branching,p,{0:['box','diamond']}),false,'box diamond order');
assert.equal(evaluate(branching,p,{0:['diamond','box']}),true,'diamond box order');
assert.equal(evaluate(branching,p,{},0),false,'no implicit reflexivity');
assert.equal(evaluate(branching,p,{0:['diamond']},1),true,'explicit self loop');
const not=indexTree(unary(atom('p')));
assert.equal(evaluate(branching,not,{0:['box']}),false,'box not p');
assert.equal(evaluate(branching,not,{1:['box']}),true,'not box p');
const split={worlds:[{atoms:[]},{atoms:['p']},{atoms:['q']}],edges:[[0,1],[0,2]],actual:0};
const and=indexTree(binary('and',atom('p'),atom('q')));
assert.equal(evaluate(split,and,{0:['diamond']}),false,'diamond of conjunction requires one common witness');
assert.equal(evaluate(split,and,{1:['diamond'],2:['diamond']}),true,'conjunction of diamonds can have different witnesses');
assert.equal(format(and,{0:['box'],1:['diamond']}),'□(◇p ∧ q)');
assert.equal(validInventory({0:['diamond','box']},{diamond:1,box:1}),true);
assert.equal(validInventory({0:['diamond']},{diamond:1,box:1}),false);

// Exhaust all two-world relations and valuations with nested stack orders.
for(let rel=0;rel<16;rel++) for(let val=0;val<16;val++) {
  const model={actual:0,worlds:[0,1].map(i=>({atoms:['p','q'].filter((_,j)=>val&(1<<(i*2+j)))})),edges:[]};
  for(let a=0;a<2;a++)for(let b=0;b<2;b++)if(rel&(1<<(a*2+b)))model.edges.push([a,b]);
  for(const type of ['and','or','implies']) {
    const formula=indexTree(binary(type,unary(atom('p')),atom('q')));
    for(const placement of [{},{0:['box','diamond']},{0:['diamond','box']},{1:['diamond'],3:['box']},{2:['box','diamond'],3:['diamond']}]) {
      const expected=truthSet(model,formula,placement);
      for(let w=0;w<2;w++)assert.equal(evaluate(model,formula,placement,w),expected.has(w));
    }
  }
}
let generated=0;
for(let seed=0;seed<100;seed++)for(let level=1;level<=40;level++) {
  const puzzle=generatePuzzle(level,seed);
  assert.ok(check(puzzle,puzzle.witness),`witness seed ${seed} level ${level}`);
  assert.ok(truthSet(puzzle.model,puzzle.formula,puzzle.witness).has(puzzle.model.actual),'independent oracle validates witness');
  assert.equal(evaluate(puzzle.model,puzzle.formula),false,'unmodified formula must be false');
  assert.equal(check(puzzle,{}),false,'must use every given operator');
  assert.equal(check(puzzle,{999:Object.values(puzzle.witness).flat()}),false,'unknown slot rejected');
  assert.equal(new Set(nodes(puzzle.formula).map(n=>n.id)).size,nodes(puzzle.formula).length);
  if(seed===0)assert.deepEqual(generatePuzzle(level,seed),puzzle,'reproducible after reload');
  generated++;
}
console.log(`Modal semantics passed exhaustive two-world checks; ${generated} generated puzzles independently verified.`);
