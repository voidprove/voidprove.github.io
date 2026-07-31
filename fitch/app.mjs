import { checkProof } from "./checker.mjs?v=review6";
import {
  analyzeRuleUsage,
  checkChallengeProof,
} from "./challenge-checker.mjs?v=review6";
import {
  citationReferencesLine,
  makeSubproofAssumption,
  moveLineToParentScope,
  pathForNextLine,
  shiftCitationsForAddedPremise,
  shiftCitationsForRemovedPremise,
} from "./editor-model.mjs?v=review6";
import { createPropositionalChallengeSampler } from "./propositional-challenges.mjs?v=review6";

const RULE_GROUPS = Object.freeze([
  {
    label: "命题逻辑基本规则",
    rules: [
      ["reiteration", "重申", "行号"],
      ["and-intro", "合取引入", "行号, 行号"],
      ["and-elim", "合取消去", "行号"],
      ["or-intro", "析取引入", "行号"],
      ["or-elim", "析取消去", "行号, 起始-末行, 起始-末行"],
      ["implies-intro", "条件引入", "起始-末行"],
      ["implies-elim", "条件消去", "行号, 行号"],
      ["iff-intro", "双条件引入", "起始-末行, 起始-末行"],
      ["iff-elim", "双条件消去", "行号, 行号"],
      ["not-intro", "否定引入", "起始-末行"],
      ["indirect-proof", "反证法", "起始-末行"],
    ],
  },
  {
    label: "量词与等同",
    rules: [
      ["forall-intro", "全称引入", "行号"],
      ["forall-elim", "全称消去", "行号"],
      ["exists-intro", "存在引入", "行号"],
      ["exists-elim", "存在消去", "行号, 起始-末行"],
      ["identity-intro", "等同引入", "无需引用"],
      ["identity-elim", "等同消去", "行号, 行号"],
    ],
  },
  {
    label: "派生规则",
    rules: [
      ["disjunctive-syllogism", "析取三段论", "行号, 行号"],
      ["modus-tollens", "否定后件式", "行号, 行号"],
      ["double-negation", "双重否定消去", "行号"],
      ["excluded-middle", "排中律", "起始-末行, 起始-末行"],
      ["demorgan", "德摩根律", "行号"],
      ["quantifier-conversion", "量词转换", "行号"],
    ],
  },
]);

const CITATION_HINTS = new Map(
  RULE_GROUPS.flatMap((group) =>
    group.rules.map(([id, _label, hint]) => [id, hint]),
  ),
);

const elements = {
  premiseList: document.querySelector("#premise-list"),
  premiseTemplate: document.querySelector("#premise-row-template"),
  proofLines: document.querySelector("#proof-lines"),
  addPremise: document.querySelector("#add-premise"),
  addLine: document.querySelector("#add-line"),
  startSubproof: document.querySelector("#start-subproof"),
  exitSubproof: document.querySelector("#exit-subproof"),
  deleteLastLine: document.querySelector("#delete-last-line"),
  checkProof: document.querySelector("#check-proof"),
  feedback: document.querySelector("#feedback"),
  feedbackTitle: document.querySelector("#feedback-title"),
  feedbackMessage: document.querySelector("#feedback-message"),
  actionStatus: document.querySelector("#action-status"),
  liveRegion: document.querySelector("#live-region"),
  symbolPalette: document.querySelector(".symbol-palette"),
  modeInputs: [...document.querySelectorAll('input[name="editor-mode"]')],
  challengePanel: document.querySelector("#challenge-panel"),
  challengePremiseSummary: document.querySelector("#challenge-premise-summary"),
  challengeConclusion: document.querySelector("#challenge-conclusion"),
  newChallenge: document.querySelector("#new-challenge"),
};

const state = {
  mode: "free",
  challenge: null,
  premises: [{ id: 1, formula: "" }],
  lines: [
    {
      id: 1,
      formula: "",
      rule: "reiteration",
      citations: "",
      path: [],
      isAssumption: false,
    },
  ],
  nextPremiseId: 2,
  nextLineId: 2,
  nextScopeId: 1,
  activeFormulaInput: null,
  markedDerivedLineIds: new Set(),
};

const savedWorkspaces = {
  free: null,
  test: null,
};

const challengeSampler = createPropositionalChallengeSampler();
const MAX_DIFFERENT_CHALLENGE_ATTEMPTS = 6;

function blankProofLine(id = 1) {
  return {
    id,
    formula: "",
    rule: "reiteration",
    citations: "",
    path: [],
    isAssumption: false,
  };
}

function captureWorkspace() {
  return {
    challenge: state.challenge,
    premises: state.premises,
    lines: state.lines,
    nextPremiseId: state.nextPremiseId,
    nextLineId: state.nextLineId,
    nextScopeId: state.nextScopeId,
  };
}

function restoreWorkspace(workspace) {
  state.challenge = workspace.challenge;
  state.premises = workspace.premises;
  state.lines = workspace.lines;
  state.nextPremiseId = workspace.nextPremiseId;
  state.nextLineId = workspace.nextLineId;
  state.nextScopeId = workspace.nextScopeId;
  state.activeFormulaInput = null;
  state.markedDerivedLineIds.clear();
}

function challengeKey(challenge) {
  return `${challenge.premises.join(";")}⊢${challenge.conclusion}`;
}

function sampleDifferentChallenge(previous = null) {
  const previousKey = previous ? challengeKey(previous) : null;
  let challenge;
  for (
    let attempt = 0;
    attempt < MAX_DIFFERENT_CHALLENGE_ATTEMPTS;
    attempt += 1
  ) {
    challenge = challengeSampler.sample();
    if (challengeKey(challenge) !== previousKey) return challenge;
  }
  return challenge;
}

function createTestWorkspace(previousChallenge = null) {
  const challenge = sampleDifferentChallenge(previousChallenge);
  return {
    challenge,
    premises: challenge.premises.map((formula, index) => ({
      id: index + 1,
      formula,
    })),
    lines: [blankProofLine()],
    nextPremiseId: challenge.premises.length + 1,
    nextLineId: 2,
    nextScopeId: 1,
  };
}

function premiseNumber(index) {
  return index + 1;
}

function proofLineNumber(index) {
  return state.premises.length + index + 1;
}

function autoSize(textarea) {
  textarea.style.height = "auto";
  textarea.style.height = `${Math.max(40, textarea.scrollHeight)}px`;
}

function invalidateResult() {
  elements.feedback.hidden = true;
  elements.feedback.className = "feedback";
  elements.actionStatus.textContent = "";
  elements.actionStatus.className = "action-status";
  state.markedDerivedLineIds.clear();
  document
    .querySelectorAll(
      ".proof-line--error, .proof-line--derived, .premise-row--error",
    )
    .forEach((row) =>
      row.classList.remove(
        "proof-line--error",
        "proof-line--derived",
        "premise-row--error",
      ),
    );
  document.querySelectorAll(".line-marker").forEach((marker) => {
    marker.textContent = "";
    marker.removeAttribute("aria-label");
    marker.setAttribute("aria-hidden", "true");
  });
  document
    .querySelectorAll(".line-error-message")
    .forEach((message) => message.remove());
  document
    .querySelectorAll('[aria-describedby^="line-error-"]')
    .forEach((input) => input.removeAttribute("aria-describedby"));
}

function updateCitationTexts(transformer) {
  for (const line of state.lines) {
    line.citations = transformer(line.citations);
  }
}

function setActionStatus(message, kind = "") {
  elements.actionStatus.textContent = message;
  elements.actionStatus.className = `action-status${
    kind ? ` action-status--${kind}` : ""
  }`;
}

function showNotice(title, message) {
  elements.feedback.hidden = false;
  elements.feedback.className = "feedback feedback--error";
  elements.feedbackTitle.textContent = title;
  elements.feedbackMessage.textContent = message;
  setActionStatus(message, "error");
  elements.liveRegion.textContent = `${title}：${message}`;
}

function rememberFormulaInput(textarea) {
  state.activeFormulaInput = textarea;
}

function renderPremises({ focusId = null } = {}) {
  elements.premiseList.replaceChildren();
  const fixed = state.mode === "test";

  state.premises.forEach((premise, index) => {
    const row = elements.premiseTemplate.content.firstElementChild.cloneNode(true);
    row.dataset.premiseId = String(premise.id);
    row.classList.toggle("premise-row--fixed", fixed);

    const number = row.querySelector(".line-number");
    number.textContent = String(premiseNumber(index));

    const premiseLabel = row.querySelector(".premise-label");
    premiseLabel.textContent = fixed ? "固定前提" : "前提";

    const label = row.querySelector("label");
    const textarea = row.querySelector("textarea");
    const inputId = `premise-${premise.id}`;
    label.htmlFor = inputId;
    label.textContent = fixed
      ? `第 ${premiseNumber(index)} 行测试前提，只读`
      : `第 ${premiseNumber(index)} 行前提`;
    textarea.id = inputId;
    textarea.value = premise.formula;
    textarea.placeholder = fixed ? "" : "例如：∀x(P(x) → Q(x))";
    textarea.readOnly = fixed;
    if (fixed) {
      textarea.setAttribute("aria-readonly", "true");
    } else {
      textarea.addEventListener("focus", () => rememberFormulaInput(textarea));
      textarea.addEventListener("input", () => {
        premise.formula = textarea.value;
        autoSize(textarea);
        invalidateResult();
      });
    }

    const remove = row.querySelector(".remove-premise");
    remove.hidden = fixed;
    remove.disabled = fixed;
    remove.setAttribute("aria-label", `删除第 ${premiseNumber(index)} 行前提`);
    if (!fixed) {
      remove.addEventListener("click", () => {
        const removedNumber = premiseNumber(index);
        const isCited = state.lines.some((line) =>
          citationReferencesLine(line.citations, removedNumber),
        );
        if (isCited) {
          invalidateResult();
          showNotice(
            "暂不能删除前提",
            `第 ${removedNumber} 行仍被证明引用；请先修改相关引用。`,
          );
          row.classList.add("premise-row--error");
          const inlineMessage = document.createElement("p");
          inlineMessage.className = "line-error-message";
          inlineMessage.id = `line-error-${removedNumber}`;
          inlineMessage.textContent = `第 ${removedNumber} 行仍被证明引用；请先修改相关引用。`;
          row.append(inlineMessage);
          row
            .querySelector("textarea")
            ?.setAttribute("aria-describedby", inlineMessage.id);
          return;
        }

        updateCitationTexts((citations) =>
          shiftCitationsForRemovedPremise(citations, removedNumber),
        );
        state.premises = state.premises.filter(
          (item) => item.id !== premise.id,
        );
        invalidateResult();
        renderPremises();
        renderProof();
      });
    }

    elements.premiseList.append(row);
    autoSize(textarea);
    if (!fixed && premise.id === focusId) {
      textarea.focus();
    }
  });
}

function createRuleSelect(line, lineNumber) {
  const select = document.createElement("select");
  select.className = "rule-select";
  select.setAttribute("aria-label", `第 ${lineNumber} 行使用的规则`);

  if (line.isAssumption) {
    const option = document.createElement("option");
    option.value = "assumption";
    option.textContent = "假设";
    select.append(option);
    select.value = "assumption";
    select.disabled = true;
    return select;
  }

  for (const group of RULE_GROUPS) {
    const optgroup = document.createElement("optgroup");
    optgroup.label = group.label;
    for (const [id, label] of group.rules) {
      const option = document.createElement("option");
      option.value = id;
      option.textContent = label;
      optgroup.append(option);
    }
    select.append(optgroup);
  }
  select.value = line.rule;
  select.addEventListener("change", () => {
    line.rule = select.value;
    const citation = select.closest(".proof-line").querySelector(".citation-input");
    citation.placeholder = CITATION_HINTS.get(line.rule) ?? "行号";
    invalidateResult();
  });
  return select;
}

function createProofLine(line, index, previousLine = null, nextLine = null) {
  const numberValue = proofLineNumber(index);
  const row = document.createElement("div");
  row.className = "proof-line";
  row.dataset.lineId = String(line.id);
  row.dataset.lineNumber = String(numberValue);
  row.dataset.scopeDepth = String(line.path.length);
  row.setAttribute("role", "group");
  row.setAttribute(
    "aria-label",
    line.path.length > 0
      ? `第 ${numberValue} 行，第 ${line.path.length} 层子证明${line.isAssumption ? "假设" : ""}`
      : `第 ${numberValue} 行，主证明`,
  );
  if (line.isAssumption) row.classList.add("proof-line--assumption");

  const number = document.createElement("span");
  number.className = "line-number";
  number.textContent = String(numberValue);

  const scopeGutter = document.createElement("span");
  scopeGutter.className = "scope-gutter";
  scopeGutter.setAttribute("aria-hidden", "true");
  line.path.forEach((scopeId, scopeIndex) => {
    const rail = document.createElement("span");
    rail.className = "scope-rail";
    if (previousLine?.path[scopeIndex] !== scopeId) {
      rail.classList.add("scope-rail--start");
    }
    if (nextLine?.path[scopeIndex] !== scopeId) {
      rail.classList.add("scope-rail--end");
    }
    rail.style.setProperty("--scope-index", String(scopeIndex + 1));
    scopeGutter.append(rail);
  });
  row.style.setProperty("--scope-width", `${line.path.length * 20}px`);

  const formulaLabel = document.createElement("label");
  formulaLabel.className = "sr-only";
  const formulaId = `proof-formula-${line.id}`;
  formulaLabel.htmlFor = formulaId;
  formulaLabel.textContent = `第 ${numberValue} 行公式`;

  const formula = document.createElement("textarea");
  formula.id = formulaId;
  formula.rows = 1;
  formula.spellcheck = false;
  formula.autocapitalize = "off";
  formula.value = line.formula;
  formula.placeholder = line.isAssumption ? "输入假设" : "输入公式";
  formula.addEventListener("focus", () => rememberFormulaInput(formula));
  formula.addEventListener("input", () => {
    line.formula = formula.value;
    autoSize(formula);
    invalidateResult();
  });

  const rule = createRuleSelect(line, numberValue);

  const citationLabel = document.createElement("label");
  citationLabel.className = "sr-only";
  const citationId = `proof-citation-${line.id}`;
  citationLabel.htmlFor = citationId;
  citationLabel.textContent = `第 ${numberValue} 行引用`;

  const citations = document.createElement("input");
  citations.id = citationId;
  citations.className = "citation-input";
  citations.type = "text";
  citations.autocomplete = "off";
  citations.value = line.citations;
  citations.placeholder = line.isAssumption
    ? "无需引用"
    : (CITATION_HINTS.get(line.rule) ?? "行号");
  citations.disabled = line.isAssumption;
  citations.setAttribute("aria-label", `第 ${numberValue} 行引用`);
  citations.addEventListener("input", () => {
    line.citations = citations.value;
    invalidateResult();
  });

  const marker = document.createElement("span");
  marker.className = "line-marker";
  marker.setAttribute("aria-hidden", "true");

  row.append(
    number,
    scopeGutter,
    formulaLabel,
    formula,
    rule,
    citationLabel,
    citations,
    marker,
  );
  queueMicrotask(() => autoSize(formula));
  return row;
}

function applyDerivedMarkers(ruleUsage) {
  for (const occurrence of ruleUsage?.derivedOccurrences ?? []) {
    const line = state.lines[occurrence.lineIndex];
    if (!line) continue;
    state.markedDerivedLineIds.add(line.id);
    const row = elements.proofLines.querySelector(
      `[data-line-id="${line.id}"]`,
    );
    const marker = row?.querySelector(".line-marker");
    if (!row || !marker) continue;
    row.classList.add("proof-line--derived");
    marker.textContent = "派生";
    marker.removeAttribute("aria-hidden");
    marker.setAttribute(
      "aria-label",
      `第 ${occurrence.lineNumber} 行使用派生规则${occurrence.label}`,
    );
    marker.title = `派生规则：${occurrence.label}`;
  }
}

function renderProof({ focusLast = false } = {}) {
  if (state.lines.length === 0) {
    const empty = document.createElement("p");
    empty.className = "empty-proof";
    empty.textContent = "添加第一行开始证明";
    elements.proofLines.replaceChildren(empty);
    updateStructureButtons();
    return;
  }

  elements.proofLines.replaceChildren(
    ...state.lines.map((line, index) =>
      createProofLine(
        line,
        index,
        state.lines[index - 1] ?? null,
        state.lines[index + 1] ?? null,
      ),
    ),
  );
  updateStructureButtons();

  if (focusLast) {
    const last = state.lines.at(-1);
    const input = document.querySelector(`#proof-formula-${last.id}`);
    input?.focus();
    input?.setSelectionRange(input.value.length, input.value.length);
  }
}

function updateStructureButtons() {
  const last = state.lines.at(-1);
  elements.startSubproof.disabled = !last || last.isAssumption;
  elements.exitSubproof.disabled = !last || last.path.length === 0;
  elements.deleteLastLine.disabled = !last;
}

function updateModeUI() {
  const testing = state.mode === "test";
  elements.modeInputs.forEach((input) => {
    input.checked = input.value === state.mode;
  });
  elements.addPremise.hidden = testing;
  elements.challengePanel.hidden = !testing;
  if (testing && state.challenge) {
    elements.challengePremiseSummary.textContent =
      state.challenge.premises.length === 0
        ? "无前提"
        : `${state.challenge.premises.length} 个固定前提`;
    elements.challengeConclusion.textContent = state.challenge.conclusion;
  } else {
    elements.challengePremiseSummary.textContent = "";
    elements.challengeConclusion.textContent = "";
  }
}

function renderWorkspace({ focusProof = false } = {}) {
  updateModeUI();
  renderPremises();
  renderProof({ focusLast: focusProof });
}

function switchMode(mode) {
  if (!Object.hasOwn(savedWorkspaces, mode) || mode === state.mode) return;
  invalidateResult();
  savedWorkspaces[state.mode] = captureWorkspace();
  if (!savedWorkspaces[mode]) {
    savedWorkspaces[mode] =
      mode === "test"
        ? createTestWorkspace()
        : {
            challenge: null,
            premises: [{ id: 1, formula: "" }],
            lines: [blankProofLine()],
            nextPremiseId: 2,
            nextLineId: 2,
            nextScopeId: 1,
          };
  }
  state.mode = mode;
  restoreWorkspace(savedWorkspaces[mode]);
  renderWorkspace({ focusProof: true });
  elements.liveRegion.textContent =
    mode === "test"
      ? `已进入随机测试。目标结论：${state.challenge.conclusion}`
      : "已返回自由编辑。";
}

function newChallenge() {
  if (state.mode !== "test") return;
  invalidateResult();
  const workspace = createTestWorkspace(state.challenge);
  savedWorkspaces.test = workspace;
  restoreWorkspace(workspace);
  renderWorkspace({ focusProof: true });
  elements.liveRegion.textContent = `已生成新题。目标结论：${state.challenge.conclusion}`;
}

function addPremise() {
  if (state.mode === "test") return;
  const previousPremiseCount = state.premises.length;
  updateCitationTexts((citations) =>
    shiftCitationsForAddedPremise(citations, previousPremiseCount),
  );
  const premise = { id: state.nextPremiseId, formula: "" };
  state.nextPremiseId += 1;
  state.premises.push(premise);
  invalidateResult();
  renderPremises({ focusId: premise.id });
  renderProof();
}

function addLine() {
  const line = {
    id: state.nextLineId,
    formula: "",
    rule: "reiteration",
    citations: "",
    path: pathForNextLine(state.lines),
    isAssumption: false,
  };
  state.nextLineId += 1;
  state.lines.push(line);
  invalidateResult();
  renderProof({ focusLast: true });
}

function startSubproof() {
  const last = state.lines.at(-1);
  if (!last || last.isAssumption) return;
  state.lines[state.lines.length - 1] = makeSubproofAssumption(
    last,
    `scope-${state.nextScopeId}`,
  );
  state.nextScopeId += 1;
  invalidateResult();
  renderProof({ focusLast: true });
  elements.liveRegion.textContent = `第 ${proofLineNumber(state.lines.length - 1)} 行已设为新子证明的假设。`;
}

function exitSubproof() {
  const last = state.lines.at(-1);
  if (!last || last.path.length === 0) return;
  state.lines[state.lines.length - 1] = moveLineToParentScope(last);
  invalidateResult();
  renderProof({ focusLast: true });
  elements.liveRegion.textContent = `第 ${proofLineNumber(state.lines.length - 1)} 行已移到上一层证明。`;
}

function deleteLastLine() {
  if (state.lines.length === 0) return;
  state.lines.pop();
  invalidateResult();
  renderProof({ focusLast: state.lines.length > 0 });
}

function resultLineNumber(error) {
  if (Number.isInteger(error?.lineNumber)) return error.lineNumber;
  if (Number.isInteger(error?.premiseNumber)) return error.premiseNumber;
  if (Number.isInteger(error?.lineIndex)) {
    return state.premises.length + error.lineIndex + 1;
  }
  if (Number.isInteger(error?.premiseIndex)) return error.premiseIndex + 1;
  return null;
}

function derivedUsageSummary(ruleUsage) {
  const occurrences = ruleUsage?.derivedOccurrences ?? [];
  if (occurrences.length === 0) return "未使用派生规则。";
  return `使用了派生规则：${occurrences
    .map(({ lineNumber, label }) => `第 ${lineNumber} 行 ${label}`)
    .join("；")}。`;
}

function showCheckResult(result) {
  elements.feedback.hidden = false;
  if (result.ok) {
    elements.feedback.className = "feedback feedback--success";
    elements.feedbackTitle.textContent =
      state.mode === "test" ? "测试通过" : "证明成立";
    const proofSummary =
      state.mode === "test"
        ? "证明有效，且末行是指定结论。"
        : `全部 ${state.lines.length} 个证明步骤均符合所选规则。`;
    const usageSummary = derivedUsageSummary(result.ruleUsage);
    elements.feedbackMessage.textContent = `${proofSummary}${usageSummary}`;
    setActionStatus(
      result.ruleUsage?.usesDerivedRules
        ? "证明成立（含派生规则）"
        : "证明成立（未用派生规则）",
      "success",
    );
    elements.liveRegion.textContent = `证明检查通过。${usageSummary}`;
    return;
  }

  const error = result.error ?? result;
  const lineNumber = resultLineNumber(error);
  const prefix = lineNumber === null ? "" : `第 ${lineNumber} 行：`;
  elements.feedback.className = "feedback feedback--error";
  elements.feedbackTitle.textContent =
    error.kind === "goal"
      ? "尚未得到目标结论"
      : error.kind === "challenge-config"
        ? "测试题配置有误"
        : error.kind === "signature"
          ? "语法警告"
          : error.kind === "syntax"
            ? "语法有误"
            : "证明尚未成立";
  elements.feedbackMessage.textContent = `${prefix}${error.message ?? "无法验证这一证明步骤。"}`;
  setActionStatus(elements.feedbackMessage.textContent, "error");
  elements.liveRegion.textContent = elements.feedbackMessage.textContent;

  if (lineNumber !== null) {
    const premiseCount = state.premises.length;
    let row;
    if (lineNumber <= premiseCount) {
      row = elements.premiseList.children[lineNumber - 1];
      row?.classList.add("premise-row--error");
    } else {
      row = elements.proofLines.querySelector(
        `[data-line-number="${lineNumber}"]`,
      );
      row?.classList.add("proof-line--error");
    }
    if (row) {
      const inlineMessage = document.createElement("p");
      inlineMessage.className = "line-error-message";
      inlineMessage.id = `line-error-${lineNumber}`;
      inlineMessage.textContent = error.message ?? "无法验证这一证明步骤。";
      row.append(inlineMessage);
      row
        .querySelector("textarea")
        ?.setAttribute("aria-describedby", inlineMessage.id);
    }
    const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    row?.scrollIntoView({
      behavior: reducedMotion ? "auto" : "smooth",
      block: "center",
    });
    const formulaInput = row?.querySelector("textarea");
    formulaInput?.focus({ preventScroll: true });
    if (
      formulaInput &&
      Number.isInteger(error.position) &&
      Number.isInteger(error.end)
    ) {
      formulaInput.setSelectionRange(error.position, error.end);
    }
  }
}

function runCheck() {
  invalidateResult();
  const proofLines = state.lines.map((line) => ({
    id: line.id,
    formula: line.formula,
    rule: line.isAssumption ? "assumption" : line.rule,
    citations: line.citations,
    path: [...line.path],
    isAssumption: line.isAssumption,
  }));
  let result;
  if (state.mode === "test") {
    result = checkChallengeProof({
      premises: [...state.challenge.premises],
      target: state.challenge.conclusion,
      lines: proofLines,
    });
  } else {
    const premises = state.premises.map((premise) => premise.formula);
    result = {
      ...checkProof({ premises, lines: proofLines }),
      ruleUsage: analyzeRuleUsage(proofLines, premises.length),
    };
  }
  if (result.ok) applyDerivedMarkers(result.ruleUsage);
  showCheckResult(result);
}

function insertSymbol(symbol) {
  let input = state.activeFormulaInput;
  if (!input?.isConnected || input.readOnly || input.disabled) {
    const lastLine = state.lines.at(-1);
    input = lastLine
      ? document.querySelector(`#proof-formula-${lastLine.id}`)
      : state.mode === "free"
        ? elements.premiseList.querySelector("textarea")
        : null;
  }
  if (!input || input.readOnly || input.disabled) return;

  const start = input.selectionStart ?? input.value.length;
  const end = input.selectionEnd ?? start;
  input.setRangeText(symbol, start, end, "end");
  input.dispatchEvent(new Event("input", { bubbles: true }));
  input.focus();
}

elements.addPremise.addEventListener("click", addPremise);
elements.addLine.addEventListener("click", addLine);
elements.startSubproof.addEventListener("click", startSubproof);
elements.exitSubproof.addEventListener("click", exitSubproof);
elements.deleteLastLine.addEventListener("click", deleteLastLine);
elements.checkProof.addEventListener("click", runCheck);
elements.newChallenge.addEventListener("click", newChallenge);
elements.modeInputs.forEach((input) => {
  input.addEventListener("change", () => {
    if (input.checked) switchMode(input.value);
  });
});
elements.symbolPalette.addEventListener("click", (event) => {
  const button = event.target.closest("button[data-symbol]");
  if (button) insertSymbol(button.dataset.symbol);
});

savedWorkspaces.free = captureWorkspace();
renderWorkspace();
