# Modal Lab

A dependency-free browser game for finite pointed Kripke models in normal modal logic K.

Serve the repository with a static HTTP server and open `/modal-lab/`. The Hakyll configuration copies this directory into the generated website. No compilation or backend is required for the app.

Players use the exact supplied inventory of diamonds and boxes. Every syntax-tree node has an insertion point marked by a small caret below the gap just before its opening symbol; the symbol and the area around the caret are clickable drop targets. Operators stacked in one slot are read outside-in, left to right; a slot before a parenthesized expression scopes over the whole expression. Drag tokens between the bank and slots, or select a token and activate a slot with the mouse, touch, or keyboard. Clicking a placed token returns it to the bank.

The distinguished actual world is w₀. Atoms shown in a world are precisely those true there; ∅ means none. Only drawn directed edges belong to the accessibility relation. Reciprocal edges share a line with an arrowhead at each end; the model checker still evaluates the two directions separately. Boxes are vacuously true at dead ends; diamonds are false there. Model inspection does not change the actual world.

The first two levels introduce diamond and box. Later levels generate random models and propositional formula trees with two, three, then four modal operators. Generated questions have a false base formula, a verified satisfying placement, and (outside the introductory levels) a failing placement. A bounded generator with a constructive fallback guarantees termination and solvability. Difficulty is increased structurally, not calibrated to human solve times. Any valid placement is accepted, not just the generator's witness. Hint text can reveal parts of a witness.

The seed, current level, and unlock progress are saved in localStorage. This is local game state, not an assessment or secure scoring system. New browsers get a new seed. Fonts are optional Google Fonts requests with system fallbacks; all game logic and assets are local.

Run `node tests/modal-lab.test.mjs` from the repository root. Tests include modal vacuity, nonreflexive frames, self loops, scope, operator order, exact inventories, exhaustive small-model comparisons to an independent truth-set evaluator, and 4,000 generated solvability checks.
