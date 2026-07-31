import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { RULE_OPTIONS } from "../fitch/checker.mjs";

const root = resolve(import.meta.dirname, "..");
const html = readFileSync(resolve(root, "fitch/index.html"), "utf8");
const app = readFileSync(resolve(root, "fitch/app.mjs"), "utf8");
const challengeChecker = readFileSync(
  resolve(root, "fitch/challenge-checker.mjs"),
  "utf8",
);
const challengeGenerator = readFileSync(
  resolve(root, "fitch/propositional-challenges.mjs"),
  "utf8",
);
const challengeDifficulty = readFileSync(
  resolve(root, "fitch/challenge-difficulty.mjs"),
  "utf8",
);
const styles = readFileSync(resolve(root, "fitch/styles.css"), "utf8");
const site = readFileSync(resolve(root, "site.hs"), "utf8");

const ids = [...html.matchAll(/\bid="([^"]+)"/gu)].map((match) => match[1]);
assert.equal(new Set(ids).size, ids.length, "HTML IDs must be unique");

const queriedIds = [
  ...app.matchAll(/querySelector\("#([A-Za-z0-9_-]+)"\)/gu),
].map((match) => match[1]);
for (const id of queriedIds) {
  assert.ok(ids.includes(id), `app queries missing #${id}`);
}

for (const match of html.matchAll(/aria-labelledby="([^"]+)"/gu)) {
  for (const id of match[1].split(/\s+/u)) {
    assert.ok(ids.includes(id), `aria-labelledby points to missing #${id}`);
  }
}

const editorRuleIds = [
  ...app.matchAll(/^\s*\["([a-z-]+)",\s*"[^"]+",\s*"[^"]+"\],?$/gmu),
].map((match) => match[1]);
const checkerRuleIds = RULE_OPTIONS.filter(({ id }) => id !== "assumption").map(
  ({ id }) => id,
);
assert.deepEqual(
  [...editorRuleIds].sort(),
  [...checkerRuleIds].sort(),
  "dropdown and checker rule IDs must stay in sync",
);

for (const match of app.matchAll(/from\s+"(\.\/[^"?]+)(?:\?[^"\s]+)?"/gu)) {
  const importedPath = resolve(root, "fitch", match[1]);
  readFileSync(importedPath);
}

assert.match(site, /match "fitch\/\*"/u);
assert.match(html, /id="premise-list"/u);
assert.match(html, /id="proof-lines"/u);
assert.match(html, /id="check-proof"/u);
assert.match(html, /<main id="editor" class="page" tabindex="-1">/u);
assert.match(html, /name="editor-mode" value="free" checked/u);
assert.match(html, /name="editor-mode" value="test"/u);
assert.match(html, /id="challenge-panel"[^>]*hidden/su);
assert.match(html, /id="challenge-conclusion"/u);
assert.match(html, /id="challenge-conclusion"[\s\S]*?tabindex="0"/u);
assert.match(html, /id="new-challenge"/u);
assert.match(html, /data-symbol="∀"/u);
for (const command of [
  String.raw`\forall`,
  String.raw`\exists`,
  String.raw`\not`,
  String.raw`\and`,
  String.raw`\or`,
  String.raw`\implies`,
  String.raw`\iff`,
  String.raw`\neq`,
  String.raw`\neg`,
  String.raw`\lnot`,
  String.raw`\land`,
  String.raw`\wedge`,
  String.raw`\lor`,
  String.raw`\vee`,
  String.raw`\to`,
  String.raw`\rightarrow`,
  String.raw`\leftrightarrow`,
  String.raw`\ne`,
]) {
  assert.ok(html.includes(command), `syntax guide must document ${command}`);
}
assert.doesNotMatch(html, /data-symbol="⊥"/u);
assert.doesNotMatch(html, /矛盾|否定消去|爆炸律|间接证明/u);
assert.match(html, /反证法/u);
assert.match(html, /φ ∧ ¬φ/u);
assert.match(html, /二元联结词没有默认的优先级或结合方向/u);
assert.match(html, /\(p ∧ q\) → r/u);
assert.match(html, /p ∧ \(q → r\)/u);
assert.match(html, /不能写 <code>p ∧ q → r<\/code>/u);
assert.doesNotMatch(app, /"not-elim"|"explosion"/u);
assert.match(app, /textarea\.readOnly = fixed/u);
assert.match(app, /if \(!input \|\| input\.readOnly \|\| input\.disabled\) return/u);
assert.match(app, /premises: \[\.\.\.state\.challenge\.premises\]/u);
assert.match(app, /result = checkChallengeProof\(/u);
assert.match(app, /marker\.textContent = "派生"/u);
assert.match(app, /if \(result\.ok\) applyDerivedMarkers\(result\.ruleUsage\)/u);
assert.match(app, /savedWorkspaces\[state\.mode\] = captureWorkspace\(\)/u);
assert.match(challengeChecker, /lines\[finalIndex\]\.path\.length !== 0/u);
assert.match(challengeChecker, /alphaEquivalent\(core\.conclusion, targetAst\)/u);
assert.match(challengeChecker, /kind === "derived"/u);
assert.match(challengeGenerator, /premises:\s*\[\]/u);
assert.match(challengeGenerator, /isValidPropositionalArgument/u);
assert.match(challengeGenerator, /isSatisfiablePropositionalSet/u);
assert.match(challengeGenerator, /createPropositionalChallengeSampler/u);
assert.match(challengeDifficulty, /direct:\s*30/u);
assert.match(challengeDifficulty, /light:\s*20/u);
assert.match(challengeDifficulty, /substantial:\s*50/u);
assert.doesNotMatch(html, /difficulty|triviality|难度分|平凡度/iu);
assert.match(styles, /\.proof-line--derived \.line-marker/u);
assert.match(styles, /\.premise-row--fixed textarea/u);
const paletteIndex = html.indexOf('class="symbol-palette"');
const actionsIndex = html.indexOf('class="editor-actions"');
const sheetIndex = html.indexOf('class="fitch-sheet"');
const premiseIndex = html.indexOf('id="premise-list"');
const separatorIndex = html.indexOf('class="premise-separator"');
const proofIndex = html.indexOf('id="proof-lines"');
assert.ok(
  paletteIndex < sheetIndex && actionsIndex < sheetIndex,
  "editing tools must sit outside and before the proof sheet",
);
assert.ok(
  sheetIndex < premiseIndex && premiseIndex < separatorIndex && separatorIndex < proofIndex,
  "premises and proof lines must be consecutive within one proof sheet",
);
assert.match(
  styles,
  /\.fitch-sheet__body::before\s*\{[^}]*top:\s*4px;[^}]*bottom:\s*4px;[^}]*left:\s*45px/su,
);
assert.match(
  styles,
  /\.scope-rail\s*\{[^}]*top:\s*-1px;[^}]*bottom:\s*-1px;[^}]*left:\s*calc\(45px \+ var\(--scope-index\) \* 20px\);[^}]*border-radius:\s*0/su,
);
assert.match(styles, /\.scope-gutter\s*\{[^}]*position:\s*static/su);
assert.match(
  styles,
  /\.scope-rail--start\s*\{[^}]*top:\s*4px;[^}]*border-top-left-radius:\s*999px/su,
);
assert.match(
  styles,
  /\.scope-rail--end\s*\{[^}]*bottom:\s*4px;[^}]*border-bottom-right-radius:\s*999px/su,
);
assert.match(
  styles,
  /\.proof-line--assumption::after\s*\{[^}]*height:\s*3px;[^}]*left:\s*calc\(45px \+ var\(--scope-width\)\)/su,
);
assert.match(
  styles,
  /\.premise-separator\s*\{[^}]*height:\s*3px;[^}]*margin:\s*0 8px 0 45px/su,
);
assert.doesNotMatch(styles, /\.subproof\s*\{/u);
assert.match(app, /className = "scope-rail"/u);
assert.match(
  styles,
  /\.proof-line--assumption \.scope-rail:last-child\s*\{[^}]*bottom:\s*-1px;[^}]*border-bottom-right-radius:\s*0/su,
);

const nestedRailGeometry = styles.match(
  /left:\s*calc\((\d+)px \+ var\(--scope-index\) \* (\d+)px\)/u,
);
const rootRailGeometry = styles.match(
  /\.fitch-sheet__body::before\s*\{[^}]*left:\s*(\d+)px/su,
);
const scopeWidthGeometry = app.match(/line\.path\.length \* (\d+)/u);
assert.ok(nestedRailGeometry && rootRailGeometry && scopeWidthGeometry);
const nestedRailBase = Number(nestedRailGeometry[1]);
const railStep = Number(nestedRailGeometry[2]);
assert.equal(
  Number(scopeWidthGeometry[1]),
  railStep,
  "formula indentation and rail spacing must use the same interval",
);
assert.equal(
  nestedRailBase,
  Number(rootRailGeometry[1]),
  "nested rail positions must share the root rail's origin",
);
const railPositions = [
  Number(rootRailGeometry[1]),
  ...[1, 2, 3].map((scopeIndex) => nestedRailBase + scopeIndex * railStep),
];
assert.deepEqual(
  railPositions.slice(1).map((position, index) => position - railPositions[index]),
  [railStep, railStep, railStep],
  "root and nested scope rails must use one consistent horizontal interval",
);
assert.equal(
  (styles.match(/\{/gu) ?? []).length,
  (styles.match(/\}/gu) ?? []).length,
);

// Checking is explicitly button-driven; input handlers only invalidate stale output.
assert.equal((app.match(/checkProof\s*\(/gu) ?? []).length, 1);
assert.match(app, /elements\.checkProof\.addEventListener\("click", runCheck\)/u);

console.log(
  `Fitch UI static integration passed ${ids.length} unique IDs and ${checkerRuleIds.length} selectable rules.`,
);
