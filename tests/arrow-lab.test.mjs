import assert from 'node:assert/strict';
import test from 'node:test';
import { analyzePuzzle, evaluatePuzzle, findHint, levels } from '../arrow-lab/logic.mjs';

const level = id => levels.find(puzzle => puzzle.id === id);

test('a dead end satisfies a box and falsifies a diamond, including under nesting', () => {
  const puzzle = {
    rule: 'any',
    worlds: [
      { atoms: ['p'], formulas: ['□p', '◇p', '◇□¬p', '□◇p'] },
      { atoms: ['p'], formulas: [] },
    ],
  };
  assert.deepEqual(evaluatePuzzle(puzzle, []).worlds[0], [true, false, false, true]);
  assert.deepEqual(evaluatePuzzle(puzzle, [[0, 1]]).worlds[0], [true, true, true, false]);
});

test('frame rules report missing arrows even when every formula is true', () => {
  const worlds = Array.from({ length: 3 }, () => ({ atoms: ['p'], formulas: ['p'] }));
  const path = [[0, 1], [1, 2]];
  assert.ok(evaluatePuzzle({ rule: 'any', worlds }, path).solved);
  for (const rule of ['reflexive', 'symmetric', 'serial', 'transitive', 'equivalence']) {
    const result = evaluatePuzzle({ rule, worlds }, path);
    assert.equal(result.frameOk, false, rule);
    assert.equal(result.solved, false, rule);
    assert.ok(result.frameIssues.length, rule);
  }
  assert.ok(evaluatePuzzle({ rule: 'transitive', worlds }, [...path, [0, 2]]).solved);
  const reciprocal = [[0, 1], [1, 0]];
  assert.equal(evaluatePuzzle({ rule: 'transitive', worlds }, reciprocal).solved, false);
  assert.ok(evaluatePuzzle({ rule: 'equivalence', worlds }, [...reciprocal, [0, 0], [1, 1], [2, 2]]).solved);
});

test('the three worksheet answers are valid and other correct relations also pass', () => {
  const references = [
    ['worksheet-any', [[1, 2], [1, 3], [2, 5], [3, 4], [4, 5], [5, 2]]],
    ['worksheet-reflexive', [[1, 1], [2, 2], [3, 3], [4, 4], [5, 5], [1, 3], [3, 5], [5, 2], [2, 4], [4, 5]]],
    ['worksheet-symmetric', [[1, 2], [2, 1], [2, 3], [3, 2], [3, 4], [4, 3], [4, 5], [5, 4], [5, 1], [1, 5]]],
  ];
  for (const [id, relation] of references) {
    const puzzle = level(id);
    assert.equal(relation.length, puzzle.minimum);
    assert.ok(evaluatePuzzle(puzzle, relation.map(([from, to]) => [from - 1, to - 1])).solved, id);
  }
  const puzzle = level('one-witness');
  const nonminimal = [[0, 1], [1, 1]];
  assert.ok(nonminimal.length > puzzle.minimum);
  assert.ok(evaluatePuzzle(puzzle, nonminimal).solved);
  assert.equal(findHint(puzzle, nonminimal), null);
});

test('each advertised minimum is attainable with few minimum solutions', () => {
  for (const puzzle of levels) {
    const result = analyzePuzzle(puzzle);
    assert.equal(result.minimum, puzzle.minimum, puzzle.id);
    assert.ok(result.solutionCount >= 1 && result.solutionCount <= 3, puzzle.id);
  }
});

test('hints repair a wrong arrow and follow a compatible minimum answer', () => {
  for (const puzzle of levels) {
    // Start with arrows in both directions between all worlds, and every loop.
    const edges = puzzle.worlds.flatMap((_, from) => puzzle.worlds.map((_, to) => [from, to]));
    const maxEdits = edges.length + puzzle.minimum;
    for (let edit = 0; edit < maxEdits; edit++) {
      if (evaluatePuzzle(puzzle, edges).solved) break;
      const hint = findHint(puzzle, edges);
      assert.ok(hint, puzzle.id);
      const index = edges.findIndex(([from, to]) => hint.from === from && hint.to === to);
      if (hint.action === 'remove') {
        assert.notEqual(index, -1);
        edges.splice(index, 1);
      } else {
        assert.equal(index, -1);
        edges.push([hint.from, hint.to]);
      }
    }
    assert.ok(evaluatePuzzle(puzzle, edges).solved, puzzle.id);
  }
});
