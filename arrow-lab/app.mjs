import { evaluatePuzzle, findHint, levels, rules, worldLabel as worldName } from './logic.mjs';

const $ = (id) => document.getElementById(id);
const board = $('board');
const edgeLayer = $('edge-layer');
const worldLayer = $('world-layer');
const levelSelect = $('level-select');
const checkButton = $('check');
const storageKey = 'arrow-lab-progress-v1';
const svgNamespace = 'http://www.w3.org/2000/svg';
const ruleSymbols = { any: '→', reflexive: '↻', symmetric: '↔', serial: '⇢', transitive: '⇉', equivalence: '≋' };
const layouts = {
  3: [[.5, .22], [.75, .74], [.25, .74]],
  4: [[.5, .18], [.78, .49], [.5, .80], [.22, .49]],
  5: [[.5, .17], [.80, .48], [.73, .80], [.27, .80], [.20, .48]],
};

function readProgress() {
  try {
    return JSON.parse(localStorage.getItem(storageKey)) || {};
  } catch {
    return {};
  }
}

const saved = readProgress();
const best = Object.create(null);
const drafts = Object.create(null);
for (const level of levels) {
  const count = saved.best?.[level.id];
  if (Number.isInteger(count) && count >= level.minimum && count <= level.worlds.length ** 2) best[level.id] = count;
  const draft = saved.drafts?.[level.id];
  if (!Array.isArray(draft)) continue;
  const valid = draft.filter((edge) => Array.isArray(edge) && edge.length === 2
    && edge.every((world) => Number.isInteger(world) && world >= 0 && world < level.worlds.length));
  drafts[level.id] = [...new Map(valid.map((edge) => [edge.join(','), edge])).values()];
}

let levelIndex = Math.max(0, levels.findIndex((level) => level.id === saved.level));
let edges = [];
let history = [];
let source = null;
let hoveredEdge = null;
let pointer = null;
let ignorePointerClick = false;
let worldButtons = [];
let formulaElements = [];
let outcome = null;
let explainedHint = false;

const puzzle = () => levels[levelIndex];
const hasEdge = (from, to) => edges.some(([a, b]) => a === from && b === to);
const arrowLabel = (from, to) => from === to ? worldName(from) + ' ↻' : worldName(from) + ' → ' + worldName(to);

function saveProgress() {
  drafts[puzzle().id] = edges;
  try {
    localStorage.setItem(storageKey, JSON.stringify({ level: puzzle().id, best, drafts }));
  } catch {
    // The game is still playable when browser storage is unavailable.
  }
}

function showFeedback(message, style = '') {
  const feedback = $('feedback');
  feedback.className = 'feedback' + (style ? ' ' + style : '');
  feedback.textContent = message;
  feedback.hidden = !message;
}

function interaction(message = 'Select a world, then its destination. You can also drag.') {
  $('interaction').textContent = message;
}

function renderProgress() {
  const solved = Object.keys(best).length;
  const optimal = levels.filter((level) => best[level.id] === level.minimum).length;
  $('progress').textContent = solved + ' of ' + levels.length + ' solved' + (optimal ? ' · ' + optimal + ' at minimum' : '');
  for (const [index, option] of [...levelSelect.options].entries()) {
    const level = levels[index];
    option.textContent = (index + 1) + '. ' + level.title + (Object.hasOwn(best, level.id) ? ' ✓' : '');
  }
}

function clearEvaluation() {
  outcome = null;
  for (const { node } of formulaElements.flat()) {
    node.classList.remove('passed', 'failed');
    node.removeAttribute('aria-label');
    node.removeAttribute('title');
  }
  refreshWorldSelection();
  showFeedback('');
  $('advance').hidden = true;
}

function refreshWorldSelection() {
  for (const [index, button] of worldButtons.entries()) {
    button.classList.toggle('selected', source === index);
    button.classList.toggle('destination', pointer?.moved && pointer.target === index);
    button.setAttribute('aria-pressed', String(source === index));
    const label = [button.dataset.label];
    for (const { formula, formulaIndex } of formulaElements[index]) {
      const result = outcome ? (outcome.worlds[index][formulaIndex] ? ', true' : ', false') : '';
      label.push(formula + result);
    }
    button.setAttribute('aria-label', label.join('. '));
  }
}

function setSource(index) {
  source = index;
  refreshWorldSelection();
  renderGraph();
  if (index === null) interaction();
  else interaction('From ' + worldName(index) + ' · choose a destination or select it again for a loop.');
}

function buildWorlds() {
  const level = puzzle();
  board.dataset.worldCount = level.worlds.length;
  const positions = layouts[level.worlds.length];
  const atoms = [...new Set(level.worlds.flatMap((world) => world.formulas.join('').match(/[pqr]/g) || []))].sort();
  worldButtons = [];
  formulaElements = [];
  for (const [index, world] of level.worlds.entries()) {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'world';
    button.dataset.world = index;
    const [x, y] = positions[level.layout.indexOf(index)];
    button.style.left = x * 100 + '%';
    button.style.top = y * 100 + '%';

    const name = document.createElement('span');
    name.className = 'world-name';
    name.append('Γ');
    const number = document.createElement('sub');
    number.textContent = index + 1;
    name.append(number);

    const valuation = document.createElement('span');
    valuation.className = 'valuation';
    valuation.textContent = atoms.map((atom) => world.atoms.includes(atom) ? atom : '¬' + atom).join(', ');
    valuation.title = 'Fixed truth values';
    const formulas = document.createElement('span');
    formulas.className = 'formulas';
    const entries = [];
    for (const [formulaIndex, formula] of world.formulas.entries()) {
      if (/^¬?[pqr]$/.test(formula)) continue; // These literals are already shown in the valuation.
      const chip = document.createElement('span');
      chip.className = 'formula';
      chip.textContent = formula;
      formulas.append(chip);
      entries.push({ node: chip, formula, formulaIndex });
    }
    button.dataset.label = worldName(index) + '. ' + valuation.textContent;
    button.append(name, valuation);
    if (entries.length) button.append(formulas);
    worldButtons.push(button);
    formulaElements.push(entries);
  }
  worldLayer.replaceChildren(...worldButtons);
}

function svgElement(tag, attributes) {
  const node = document.createElementNS(svgNamespace, tag);
  for (const [name, value] of Object.entries(attributes)) node.setAttribute(name, value);
  return node;
}

const marker = svgElement('marker', {
  id: 'arrowhead', viewBox: '0 0 10 10', refX: '9', refY: '5',
  markerWidth: '5', markerHeight: '5', orient: 'auto-start-reverse',
});
marker.append(svgElement('path', { d: 'M0 0 10 5 0 10 2.4 5Z', fill: '#414eab' }));
const definitions = svgElement('defs', {});
definitions.append(marker);

function boundary(center, target, gap = 4) {
  const dx = target.x - center.x;
  const dy = target.y - center.y;
  const fraction = Math.min((center.w / 2 + gap) / Math.abs(dx), (center.h / 2 + gap) / Math.abs(dy));
  if (!Number.isFinite(fraction)) return center;
  return { x: center.x + dx * fraction, y: center.y + dy * fraction };
}

function loopPath(center, height) {
  const topSpace = center.y - center.h / 2;
  const bottomSpace = height - center.y - center.h / 2;
  const direction = topSpace > 33 && (topSpace < bottomSpace || bottomSpace < 33) ? -1 : 1;
  const y = center.y + direction * (center.h / 2 + 4);
  const x = center.x;
  return 'M ' + (x - 12) + ' ' + y + ' C ' + (x - 34) + ' ' + (y + direction * 36)
    + ', ' + (x + 34) + ' ' + (y + direction * 36) + ', ' + (x + 12) + ' ' + y;
}

function linePath(start, end) {
  return 'M ' + start.x + ' ' + start.y + ' L ' + end.x + ' ' + end.y;
}

function connectionPath(centers, from, to, bounds) {
  if (from === to) return loopPath(centers[from], bounds.height);
  const source = centers[from];
  const target = centers[to];
  const midpoint = { x: (source.x + target.x) / 2, y: (source.y + target.y) / 2 };
  const dx = target.x - source.x;
  const dy = target.y - source.y;
  const distance = Math.hypot(dx, dy);
  const obstacles = centers.filter((_, index) => index !== from && index !== to);
  const preferredSide = from < to ? 1 : -1;
  for (const offset of [0, 25, -25, 50, -50, 85, -85, 125, -125]) {
    const bend = offset * preferredSide;
    const control = { x: midpoint.x - dy / distance * bend, y: midpoint.y + dx / distance * bend };
    const start = boundary(source, control);
    const end = boundary(target, control);
    if (!clearsWorlds(start, control, end, obstacles, bounds)) continue;
    if (!offset) return linePath(start, end);
    return 'M ' + start.x + ' ' + start.y + ' Q ' + control.x + ' ' + control.y + ' ' + end.x + ' ' + end.y;
  }
  return linePath(boundary(source, target), boundary(target, source));
}

function clearsWorlds(start, control, end, obstacles, bounds) {
  // Sample the curve with a small margin so it stays clear of intervening cards.
  for (let sample = 1; sample < 40; sample++) {
    const t = sample / 40;
    const s = 1 - t;
    const x = s * s * start.x + 2 * s * t * control.x + t * t * end.x;
    const y = s * s * start.y + 2 * s * t * control.y + t * t * end.y;
    if (x < 4 || x > bounds.width - 4 || y < 4 || y > bounds.height - 4) return false;
    if (obstacles.some((card) => Math.abs(x - card.x) < card.w / 2 + 5
      && Math.abs(y - card.y) < card.h / 2 + 5)) return false;
  }
  return true;
}

function renderGraph() {
  const bounds = edgeLayer.getBoundingClientRect();
  if (!bounds.width || !bounds.height) return;
  edgeLayer.setAttribute('viewBox', '0 0 ' + bounds.width + ' ' + bounds.height);
  const centers = worldButtons.map((button) => {
    const rect = button.getBoundingClientRect();
    return { x: rect.left - bounds.left + rect.width / 2, y: rect.top - bounds.top + rect.height / 2, w: rect.width, h: rect.height };
  });
  const paths = [];
  for (const [from, to] of edges) {
    const reciprocal = from !== to && hasEdge(to, from);
    if (reciprocal && from > to) continue;
    const attributes = {
      d: connectionPath(centers, from, to, bounds),
      class: 'edge',
      'marker-end': 'url(#arrowhead)',
    };
    if (reciprocal) attributes['marker-start'] = 'url(#arrowhead)';
    if (hoveredEdge) {
      const [a, b] = hoveredEdge;
      const highlighted = (from === a && to === b) || (reciprocal && from === b && to === a);
      attributes.class += highlighted ? ' emphasized' : ' dim';
    }
    paths.push(svgElement('path', attributes));
  }
  if (pointer?.moved) {
    const start = centers[pointer.from];
    const cursor = { x: pointer.x - bounds.left, y: pointer.y - bounds.top };
    const path = pointer.target === null
      ? linePath(boundary(start, cursor, 2), cursor)
      : connectionPath(centers, pointer.from, pointer.target, bounds);
    paths.push(svgElement('path', { d: path, class: 'edge preview', 'marker-end': 'url(#arrowhead)' }));
  }
  edgeLayer.replaceChildren(definitions, ...paths);
}

function renderEdges() {
  hoveredEdge = null;
  $('arrow-count').textContent = edges.length;
  $('undo').disabled = !history.length;
  $('clear').disabled = !edges.length;
  $('empty-edges').hidden = Boolean(edges.length);
  const sorted = [...edges].sort(([a, b], [c, d]) => a - c || b - d);
  const chips = sorted.map(([from, to], index) => {
    const item = document.createElement('li');
    const chip = document.createElement('button');
    chip.type = 'button';
    chip.className = 'edge-chip';
    chip.setAttribute('aria-label', 'Remove arrow from ' + worldName(from) + ' to ' + worldName(to));
    const icon = document.createElement('span');
    icon.setAttribute('aria-hidden', 'true');
    icon.textContent = '×';
    chip.append(arrowLabel(from, to), icon);
    const highlight = () => { hoveredEdge = [from, to]; renderGraph(); };
    const unhighlight = () => { hoveredEdge = null; renderGraph(); };
    chip.addEventListener('pointerenter', highlight);
    chip.addEventListener('pointerleave', unhighlight);
    chip.addEventListener('focus', highlight);
    chip.addEventListener('blur', unhighlight);
    chip.addEventListener('click', () => {
      toggleEdge(from, to);
      const remaining = $('edge-list').querySelectorAll('button');
      (remaining[Math.min(index, remaining.length - 1)] ?? worldButtons[from]).focus({ preventScroll: true });
    });
    item.append(chip);
    return item;
  });
  $('edge-list').replaceChildren(...chips);
  renderGraph();
}

function updateEdges(next, message, record = true) {
  if (record) history.push(edges);
  edges = next;
  source = null;
  clearEvaluation();
  renderEdges();
  interaction(message);
  saveProgress();
}

function toggleEdge(from, to) {
  const exists = hasEdge(from, to);
  const next = exists ? edges.filter(([a, b]) => a !== from || b !== to) : [...edges, [from, to]];
  updateEdges(next, arrowLabel(from, to) + (exists ? ' removed.' : ' added.'));
}

function setLevel(index) {
  if (index < 0 || index >= levels.length) return;
  levelIndex = index;
  const level = puzzle();
  edges = drafts[level.id] ?? [];
  history = [];
  source = null;
  pointer = null;
  explainedHint = false;
  $('hint').textContent = 'Hint';
  resizeObserver.disconnect();
  buildWorlds();
  clearEvaluation();
  resizeObserver.observe(board);
  worldButtons.forEach((button) => resizeObserver.observe(button));
  $('level-title').textContent = level.title;
  $('rule-title').textContent = rules[level.rule].label;
  $('rule-text').textContent = rules[level.rule].description;
  $('board-rule').textContent = rules[level.rule].label + ' · ' + rules[level.rule].description;
  $('rule-icon').textContent = ruleSymbols[level.rule];
  $('minimum').textContent = level.minimum;
  $('level-position').textContent = (index + 1) + ' / ' + levels.length;
  $('previous').disabled = index === 0;
  $('next').disabled = index === levels.length - 1;
  levelSelect.value = index;
  interaction();
  renderProgress();
  renderEdges();
  saveProgress();
}

function check() {
  outcome = evaluatePuzzle(puzzle(), edges);
  for (const [world, entries] of formulaElements.entries()) {
    for (const { node, formula, formulaIndex } of entries) {
      const passed = outcome.worlds[world][formulaIndex];
      node.classList.toggle('passed', passed);
      node.classList.toggle('failed', !passed);
      node.title = formula + (passed ? ' is true' : ' is false') + ' at ' + worldName(world);
      node.setAttribute('aria-label', node.title);
    }
  }
  refreshWorldSelection();
  if (outcome.solved) {
    const id = puzzle().id;
    best[id] = Math.min(best[id] ?? Infinity, edges.length);
    saveProgress();
    renderProgress();
    const extra = edges.length - puzzle().minimum;
    const message = extra === 0 ? 'Solved at the minimum. Every formula is true.'
      : 'Solved! Can you do it with ' + extra + ' fewer ' + (extra === 1 ? 'arrow' : 'arrows') + '?';
    showFeedback(message, 'good');
    $('advance').hidden = levelIndex === levels.length - 1;
    return;
  }
  const falseWorlds = outcome.worlds.map((results, i) => results.every(Boolean) ? null : worldName(i)).filter(Boolean);
  const sentences = [];
  if (!outcome.frameOk) sentences.push(outcome.frameIssues[0] ?? 'The arrows do not yet follow the relation rule.');
  if (falseWorlds.length) sentences.push('Check the highlighted formulas at ' + falseWorlds.join(', ') + '.');
  showFeedback(sentences.join(' '), 'bad');
  $('advance').hidden = true;
}

const buttonAt = (x, y) => document.elementFromPoint(x, y)?.closest('.world');
const worldAt = (x, y) => {
  const button = buttonAt(x, y);
  return button ? Number(button.dataset.world) : null;
};
const resizeObserver = new ResizeObserver(renderGraph);

board.addEventListener('click', (event) => {
  if (ignorePointerClick && event.detail > 0) return;
  const button = event.target.closest('.world');
  if (!button) { setSource(null); return; }
  const index = Number(button.dataset.world);
  if (source === null) setSource(index);
  else toggleEdge(source, index);
});
board.addEventListener('pointerdown', (event) => {
  ignorePointerClick = false;
  const button = event.target.closest('.world');
  if (!button || !event.isPrimary || event.button !== 0) return;
  pointer = { id: event.pointerId, from: Number(button.dataset.world), startX: event.clientX, startY: event.clientY, moved: false };
});
board.addEventListener('pointermove', (event) => {
  if (pointer?.id !== event.pointerId) return;
  if (!pointer.moved && Math.hypot(event.clientX - pointer.startX, event.clientY - pointer.startY) < 8) return;
  if (!pointer.moved) {
    board.setPointerCapture(event.pointerId);
    pointer.moved = true;
    source = pointer.from;
    interaction('From ' + worldName(source) + ' · release over a world to connect.');
  }
  pointer.x = event.clientX;
  pointer.y = event.clientY;
  pointer.target = worldAt(pointer.x, pointer.y);
  refreshWorldSelection();
  renderGraph();
});
board.addEventListener('pointerup', (event) => {
  if (pointer?.id !== event.pointerId) return;
  const { from, moved } = pointer;
  pointer = null;
  if (!moved) return;
  ignorePointerClick = true;
  const target = worldAt(event.clientX, event.clientY);
  if (target === null) setSource(null);
  else toggleEdge(from, target);
});
board.addEventListener('lostpointercapture', (event) => {
  if (event.target !== board || pointer?.id !== event.pointerId) return;
  const { moved } = pointer;
  pointer = null;
  if (moved) setSource(null);
});
board.addEventListener('pointercancel', () => { pointer = null; setSource(null); });
board.addEventListener('pointerleave', () => { if (pointer && !pointer.moved) pointer = null; });
document.addEventListener('keydown', (event) => {
  if (event.key === 'Escape' && !$('guide').open) {
    pointer = null;
    setSource(null);
  }
});

for (const index of levels.keys()) {
  const option = document.createElement('option');
  option.value = index;
  levelSelect.append(option);
}
levelSelect.addEventListener('change', () => setLevel(Number(levelSelect.value)));
$('previous').addEventListener('click', () => setLevel(levelIndex - 1));
$('next').addEventListener('click', () => setLevel(levelIndex + 1));
$('advance').addEventListener('click', () => {
  setLevel(levelIndex + 1);
  $('puzzle').focus();
});
$('undo').addEventListener('click', () => updateEdges(history.pop(), 'Undid the last edit.', false));
$('clear').addEventListener('click', () => updateEdges([], 'Cleared all arrows. You can undo this.'));
$('help').addEventListener('click', () => $('guide').showModal());
checkButton.addEventListener('click', check);
$('hint').addEventListener('click', () => {
  if (!explainedHint) {
    explainedHint = true;
    $('hint').textContent = 'Show an arrow';
    showFeedback(puzzle().description);
    return;
  }
  const hint = findHint(puzzle(), edges);
  if (!hint) { check(); return; }
  showFeedback((hint.action === 'add' ? 'Try adding ' : 'Try removing ') + arrowLabel(hint.from, hint.to) + '.');
});
setLevel(levelIndex);
