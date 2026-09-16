import { generatePuzzle, evaluate, check, nodes, format } from './logic.mjs';

const $ = id => document.getElementById(id);
const symbols = {diamond:'◇',box:'□'};
const key = 'modal-lab-v1';
let saved;
try { saved = JSON.parse(localStorage.getItem(key)); } catch { /* Storage may be unavailable. */ }
const goodSave = saved && Number.isInteger(saved.seed) && saved.seed >= 0 && saved.seed <= 0xffffffff && Number.isSafeInteger(saved.unlocked) && saved.unlocked >= 1 && saved.unlocked <= 100000 && Number.isInteger(saved.current) && saved.current >= 1 && saved.current <= saved.unlocked;
const progress = goodSave ? saved : {seed:crypto.getRandomValues(new Uint32Array(1))[0],unlocked:1,current:1};
let puzzle, tokens, selected = null, inspected = 0, checked = false, solved = false, hintStep = 0;
let drag = null, suppressClick = false;
function save() { try { localStorage.setItem(key, JSON.stringify(progress)); } catch { document.querySelector('.small-note').textContent = 'Progress lasts for this session'; } }
function placement() {
  const result = {};
  tokens.filter(t => t.slot !== null).sort((a,b) => a.order-b.order).forEach(t => (result[t.slot] ??= []).push(t.type));
  return result;
}
function feedback(text, kind = '') { $('feedback').textContent = text; $('feedback').className = `feedback ${kind}`; }
function invalidate() { checked = false; solved = false; $('next').hidden = true; $('check').hidden = false; $('evaluation').hidden = true; }
function loadLevel(level) {
  if (level > progress.unlocked || level < 1) return;
  progress.current = level; puzzle = generatePuzzle(level, progress.seed);
  tokens = [...Array(puzzle.inventory.diamond).fill('diamond'),...Array(puzzle.inventory.box).fill('box')].map((type,id) => ({type,id,slot:null,order:id}));
  selected = null; inspected = puzzle.model.actual; hintStep = 0; invalidate(); save();
  feedback(level <= 2 ? 'Start with the arrows from w₀. What can you reach?' : 'Use every operator. A slot can hold more than one, read from left to right.');
  render();
}
function renderLevels() {
  const first = Math.max(1, progress.current - 2);
  $('levels').innerHTML = Array.from({length:6},(_,i) => first+i).map(n => `<button class="level ${n === progress.current ? 'current' : ''} ${n < progress.unlocked ? 'completed' : ''}" ${n > progress.unlocked ? 'disabled' : ''} ${n === progress.current ? 'aria-current="step"' : ''} aria-label="Level ${n}${n > progress.unlocked ? ', locked' : n < progress.unlocked ? ', solved' : ''}" data-level="${n}">${n < progress.unlocked && n !== progress.current ? '✓' : String(n).padStart(2,'0')}</button>`).join('');
  $('solved-count').textContent = progress.unlocked - 1;
  const name = progress.current === 1 ? 'POSSIBILITY' : progress.current === 2 ? 'NECESSITY' : progress.current <= 5 ? 'SCOPE' : progress.current <= 9 ? 'NESTING' : 'EXPLORATION';
  $('stage-label').textContent = `${String(progress.current).padStart(2,'0')} / ${name}`;
}
function tokenMarkup(t) {
  return `<button class="token ${t.type} ${selected === t.id ? 'selected' : ''}" data-token="${t.id}" aria-label="${t.type === 'box' ? 'Box' : 'Diamond'} ${t.id+1}${t.slot === null ? ', select then choose a slot' : ', placed at slot '+(t.slot+1)+', click to return'}" aria-pressed="${selected === t.id}">${symbols[t.type]}</button>`;
}
function renderFormula() {
  $('tokens').innerHTML = tokens.filter(t => t.slot === null).map(tokenMarkup).join('') || '<span class="empty-bank">All operators placed ✓</span>';
  const left = tokens.filter(t => t.slot === null).length;
  $('remaining').textContent = `${left}/${tokens.length}`;
  function node(n) {
    const inserted = tokens.filter(t => t.slot === n.id).sort((a,b)=>a.order-b.order).map(tokenMarkup).join('');
    const first = n.type === 'atom' ? n.name : n.type === 'not' ? '¬' : '(';
    const slot = `<span class="slot-wrap">${inserted}<button class="slot" data-slot="${n.id}" title="Insert before ${format(n)}" aria-label="Slot ${n.id+1}, before ${format(n)}; insert selected operator"><span class="formula-symbol ${n.type === 'atom' ? 'atom' : ''}">${first}</span><span class="slot-caret" aria-hidden="true"></span></button></span>`;
    const body = n.type === 'atom' ? '' : n.type === 'not' ? node(n.child) : `${node(n.left)}<span class="connective">${{and:'∧',or:'∨',implies:'→'}[n.type]}</span>${node(n.right)}<span>)</span>`;
    return slot + body;
  }
  $('formula').innerHTML = node(puzzle.formula);
}
const mobileGraph = window.matchMedia('(max-width: 760px)');
function graphPositions(n) {
  if (mobileGraph.matches) {
    if (n === 2) return [[90,190],[330,190]];
    if (n === 3) return [[90,190],[315,85],[315,295]];
    if (n === 4) return [[65,190],[210,70],[355,190],[210,310]];
    return Array.from({length:n}, (_,i) => {const a = Math.PI + i*2*Math.PI/n; return [210+145*Math.cos(a),190+137*Math.sin(a)];});
  }
  if (n === 2) return [[180,195],[460,195]];
  if (n === 3) return [[160,190],[440,85],[440,295]];
  if (n === 4) return [[125,190],[325,68],[520,190],[325,312]];
  return Array.from({length:n}, (_,i) => {const a = Math.PI + i*2*Math.PI/n; return [320+220*Math.cos(a),190+137*Math.sin(a)];});
}
function renderGraph() {
  const {model} = puzzle, positions = graphPositions(model.worlds.length);
  $('graph').setAttribute('viewBox', mobileGraph.matches ? '0 0 420 390' : '0 0 640 380');
  const relation = model.edges;
  $('world-count').textContent = `${model.worlds.length} worlds · ${relation.length} arrows`;
  const defs = `<defs><marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#70889c"/></marker><marker id="arrow-active" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#9ce8d1"/></marker></defs>`;
  const edges = relation.map(([a,b]) => {
    const [x,y] = positions[a], [u,v] = positions[b];
    let d;
    if (a === b) {
      d = y < 110
        ? `M ${x+29} ${y-28} C ${x+103} ${y-80},${x+103} ${y+80},${x+31} ${y+29}`
        : `M ${x-28} ${y-29} C ${x-80} ${y-103},${x+80} ${y-103},${x+29} ${y-31}`;
    }
    else {
      const dx=u-x,dy=v-y,len=Math.hypot(dx,dy),nx=dx/len,ny=dy/len;
      const bend=relation.some(([c,e])=>c===b&&e===a)?30:0;
      const sx=x+nx*44-ny*bend*.38,sy=y+ny*44+nx*bend*.38,ex=u-nx*48-ny*bend*.38,ey=v-ny*48+nx*bend*.38;
      d=`M ${sx} ${sy} Q ${(x+u)/2-ny*bend} ${(y+v)/2+nx*bend} ${ex} ${ey}`;
    }
    return `<path class="edge ${a===inspected?'highlight':''}" d="${d}" marker-end="url(#${a===inspected?'arrow-active':'arrow'})"><title>w${a} accesses w${b}</title></path>`;
  }).join('');
  const worlds = model.worlds.map((w,i) => {
    const [x,y] = positions[i], truth = checked ? evaluate(model,puzzle.formula,placement(),i) : null;
    const label = `World w${i}${i===model.actual?', actual world':''}; true atoms: ${w.atoms.join(', ')||'none'}${truth===null?'':`; formula is ${truth?'true':'false'}`}`;
    return `<g class="world ${i===model.actual?'actual':''} ${i===inspected?'inspected':''}" transform="translate(${x},${y})" tabindex="0" role="button" aria-label="${label}" data-world="${i}"><circle class="halo" r="49"/><circle class="disc" r="41"/><text class="world-name" y="-2">w<tspan baseline-shift="sub" font-size="15">${i}</tspan></text><text class="atom-label" y="21">${w.atoms.join(', ')||'∅'}</text>${i===model.actual?'<text class="actual-label" y="73">ACTUAL WORLD</text>':''}${truth===null?'':`<circle cx="33" cy="-31" r="11" fill="${truth?'#9ce8d1':'#ffc4ad'}"/><text x="33" y="-27" style="fill:#13283b;font:700 12px sans-serif">${truth?'T':'F'}</text>`}</g>`;
  }).join('');
  $('graph').innerHTML = defs + edges + worlds;
  const successors = relation.filter(e=>e[0]===inspected).map(e=>`w${e[1]}`);
  $('world-detail').innerHTML = `<strong>w${inspected}${inspected===model.actual?' · actual world':''}</strong> &nbsp;→&nbsp; ${successors.length?`Accesses ${successors.join(', ')}.`:'No accessible worlds. Boxes are true here; diamonds are false.'} &nbsp; True atoms: <strong>${model.worlds[inspected].atoms.join(', ')||'none'}</strong>.`;
}
function render() { renderLevels(); renderFormula(); renderGraph(); }
function putToken(id, slot) {
  const t = tokens.find(t=>t.id===id); if (!t) return;
  t.slot = slot; t.order = Math.max(...tokens.map(t=>t.order)) + 1; selected = null; invalidate();
  feedback(slot===null ? 'Operator returned. Try a different scope.' : `${symbols[t.type]} placed before ${format(nodes(puzzle.formula).find(n=>n.id===slot))}. ${tokens.filter(t=>t.slot===null).length ? 'Keep going—use every operator.' : 'All operators placed. Ready to check.'}`);
  renderFormula(); renderGraph();
}
document.addEventListener('click', e => {
  if (suppressClick) { suppressClick = false; return; }
  const token = e.target.closest('[data-token]'), slot = e.target.closest('[data-slot]'), world = e.target.closest('[data-world]'), level=e.target.closest('[data-level]');
  if (token) {
    const t = tokens[Number(token.dataset.token)];
    if (t.slot !== null) { const slot=t.slot; putToken(t.id,null); document.querySelector(`[data-slot="${slot}"]`)?.focus({preventScroll:true}); }
    else {selected=selected===t.id?null:t.id;renderFormula();document.querySelector(`[data-token="${t.id}"]`)?.focus({preventScroll:true});feedback(selected===null?'Selection cleared.':`${symbols[t.type]} selected. Choose a caret beneath the formula.`);}
  } else if (slot) {
    if (selected !== null) {const id=Number(slot.dataset.slot);putToken(selected,id);document.querySelector(`[data-slot="${id}"]`)?.focus({preventScroll:true});}
    else feedback('First select an operator from your inventory, then choose a caret.');
  } else if (world) {inspected=Number(world.dataset.world);renderGraph();document.querySelector(`[data-world="${inspected}"]`)?.focus({preventScroll:true});}
  else if (level) loadLevel(Number(level.dataset.level));
});
document.addEventListener('keydown', e => {
  if (e.key==='Escape') {selected=null;cancelDrag();renderFormula();}
  const world=e.target.closest('[data-world]');
  if (world&&(e.key==='Enter'||e.key===' ')) {e.preventDefault();world.dispatchEvent(new MouseEvent('click',{bubbles:true}));}
});
function clearDropStyles() {document.querySelectorAll('.drop-target,.drop-bank').forEach(n=>n.classList.remove('drop-target','drop-bank'));}
function cancelDrag() {if(drag){drag.ghost?.remove();drag.source.classList.remove('dragging');drag=null;}clearDropStyles();}
document.addEventListener('pointerdown', e => {
  const token=e.target.closest('[data-token]'); if(!token||e.button!==0) return;
  suppressClick=false;
  drag={id:Number(token.dataset.token),x:e.clientX,y:e.clientY,source:token,active:false,pointer:e.pointerId};
});
document.addEventListener('pointermove', e => {
  if(!drag||e.pointerId!==drag.pointer) return;
  if(!drag.active&&Math.hypot(e.clientX-drag.x,e.clientY-drag.y)>6){drag.active=true;drag.ghost=drag.source.cloneNode(true);drag.ghost.removeAttribute('data-token');drag.ghost.classList.add('drag-ghost');drag.ghost.setAttribute('aria-hidden','true');document.body.append(drag.ghost);drag.source.classList.add('dragging');}
  if(!drag.active) return;
  e.preventDefault();drag.ghost.style.left=`${e.clientX}px`;drag.ghost.style.top=`${e.clientY}px`;
  clearDropStyles();const hit=document.elementFromPoint(e.clientX,e.clientY);hit?.closest('[data-slot]')?.classList.add('drop-target');if(hit?.closest('#bank'))$('bank').classList.add('drop-bank');
},{passive:false});
document.addEventListener('pointerup', e => {
  if(!drag||e.pointerId!==drag.pointer) return;
  const {id,active}=drag;
  const hit=document.elementFromPoint(e.clientX,e.clientY),slot=hit?.closest('[data-slot]'),bank=hit?.closest('#bank');
  cancelDrag();
  if(active){suppressClick=true;if(slot)putToken(id,Number(slot.dataset.slot));else if(bank)putToken(id,null);setTimeout(()=>{suppressClick=false;},0);}
});
document.addEventListener('pointercancel',cancelDrag);
window.addEventListener('blur',cancelDrag);
$('reset').addEventListener('click',()=>{tokens.forEach(t=>t.slot=null);selected=null;invalidate();feedback('A clean slate. Follow the arrows and try a new placement.');renderFormula();renderGraph();});
$('check').addEventListener('click',()=>{
  const left=tokens.filter(t=>t.slot===null).length;
  if(left){feedback(`Place all your operators first. ${left} ${left===1?'operator is':'operators are'} still in the inventory.`,'bad');return;}
  checked=true;solved=check(puzzle,placement());renderGraph();
  $('evaluation').hidden=false;
  const truths=puzzle.model.worlds.map((_,i)=>`w${i}: ${evaluate(puzzle.model,puzzle.formula,placement(),i)?'true':'false'}`);
  $('evaluation').textContent=`${format(puzzle.formula,placement())}  ·  ${truths.join(' · ')}`;
  if(solved){progress.unlocked=Math.max(progress.unlocked,progress.current+1);save();renderLevels();feedback('True at w₀. Nicely reasoned—the next level is unlocked.','good');$('check').hidden=true;$('next').hidden=false;$('next').focus({preventScroll:true});}
  else feedback('False at w₀. Try changing an operator’s scope or the order of a stack. The graph now shows truth at each world.','bad');
});
$('next').addEventListener('click',()=>{if(solved){loadLevel(progress.current+1);$('formula-heading').focus({preventScroll:true});}});
$('hint').addEventListener('click',()=>{
  hintStep++;
  if(hintStep===1){const successors=puzzle.model.edges.filter(e=>e[0]===0).map(e=>`w${e[1]}`);feedback(`From w₀, inspect ${successors.join(', ')}. ◇ needs one successful neighbor; □ needs all of them. Each added operator takes another step along the arrows.`);}
  else {const witness=Object.entries(puzzle.witness);const [id,ops]=witness[(hintStep-2)%witness.length];const sub=nodes(puzzle.formula).find(n=>n.id===Number(id));document.querySelectorAll('.hint-target').forEach(el=>el.classList.remove('hint-target'));document.querySelector(`[data-slot="${id}"]`)?.classList.add('hint-target');feedback(`One solution places ${ops.map(t=>symbols[t]).join('')} at the highlighted caret, before ${format(sub)}. ${witness.length>1?'Other slots may also need operators.':'Leave the other slots empty.'}`);}
});
$('help').addEventListener('click',()=>$('help-dialog').showModal());
$('close-help').addEventListener('click',()=>$('help-dialog').close());
$('start-playing').addEventListener('click',()=>$('help-dialog').close());
mobileGraph.addEventListener('change',()=>renderGraph());
loadLevel(progress.current);
