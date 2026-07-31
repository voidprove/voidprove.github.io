import {
  describeCountermodel,
  findCountermodel,
} from "./countermodel.mjs?v=20260731";
import {
  buildFitchProof,
  formatFitchFormula,
  nestProofLines,
} from "./fol-proof.mjs?v=20260731";
import {
  formatStatement,
  generateChallenge,
} from "./logic.mjs?v=20260731";

const LETTER_TERMS = Object.freeze(["S", "M", "P", "Q", "R"]);

const elements = {
  emptyState: document.querySelector("#empty-state"),
  question: document.querySelector("#question"),
  questionNumber: document.querySelector("#question-number"),
  timer: document.querySelector("#timer"),
  premises: document.querySelector("#premises"),
  conclusion: document.querySelector("#conclusion"),
  judgmentOptions: document.querySelector("#judgment-options"),
  submit: document.querySelector("#submit-answer"),
  next: document.querySelector("#next-challenge"),
  letterMode: document.querySelector("#letter-mode"),
  modeStatus: document.querySelector("#mode-status"),
  feedback: document.querySelector("#feedback"),
  feedbackTitle: document.querySelector("#feedback-title"),
  feedbackSummary: document.querySelector("#feedback-summary"),
  correctJudgment: document.querySelector("#correct-judgment"),
  correctConclusion: document.querySelector("#correct-conclusion"),
  analysisTitle: document.querySelector("#analysis-title"),
  analysisContent: document.querySelector("#analysis-content"),
  accuracy: document.querySelector("#stat-accuracy"),
  liveRegion: document.querySelector("#live-region"),
};

const state = {
  challenge: null,
  startedAt: null,
  submitted: false,
  timerId: null,
  questionNumber: 0,
  total: 0,
  correct: 0,
  displayMode: "natural",
  analysis: null,
};

function formatDuration(milliseconds) {
  return `${(milliseconds / 1000).toFixed(1)} 秒`;
}

function formatForCurrentMode(statement) {
  return formatStatement(statement, state.challenge.terms, { mode: state.displayMode });
}

function updateTimer() {
  if (!state.startedAt || state.submitted) return;
  elements.timer.textContent = formatDuration(performance.now() - state.startedAt);
}

function startTimer() {
  window.clearInterval(state.timerId);
  state.startedAt = performance.now();
  state.timerId = window.setInterval(updateTimer, 100);
  updateTimer();
}

function stopTimer() {
  window.clearInterval(state.timerId);
  state.timerId = null;
  const elapsed = performance.now() - state.startedAt;
  elements.timer.textContent = formatDuration(elapsed);
  return elapsed;
}

function updateStats() {
  const accuracy = state.total === 0 ? null : Math.round((state.correct / state.total) * 100);
  elements.accuracy.textContent = accuracy === null ? "—" : `${accuracy}%`;
}

function selectedAnswer() {
  const selected = elements.judgmentOptions.querySelector("input:checked");
  if (!selected) return null;
  return selected.value === "true";
}

function syncSubmitState() {
  elements.submit.disabled = state.submitted || selectedAnswer() === null;
}

function renderPremises() {
  elements.premises.replaceChildren(
    ...state.challenge.premises.map((premise, index) => {
      const item = document.createElement("li");
      item.className = "premise";

      const number = document.createElement("span");
      number.className = "premise__number";
      number.textContent = String(index + 1).padStart(2, "0");

      const copy = document.createElement("span");
      copy.className = "premise__copy";
      copy.textContent = formatForCurrentMode(premise);

      item.append(number, copy);
      return item;
    }),
  );
}

function renderConclusion() {
  elements.conclusion.textContent = formatForCurrentMode(
    state.challenge.conclusion,
  );
}

function proofStatementText(formula) {
  return formatFitchFormula(formula, state.challenge.terms, {
    mode: state.displayMode,
  });
}

function createProofLine(line) {
  const row = document.createElement("div");
  row.className = "proof-line";
  row.setAttribute("role", "listitem");
  if (line.rule === "assumption") row.classList.add("proof-line--assumption");
  if (line.formula.kind === "bottom") {
    row.classList.add("proof-line--contradiction");
  }

  const number = document.createElement("span");
  number.className = "proof-line__number";
  number.textContent = String(line.number);

  const formula = document.createElement("span");
  formula.className = "proof-line__formula";
  formula.textContent = proofStatementText(line.formula);

  const reason = document.createElement("span");
  reason.className = "proof-line__reason";
  const citations = [
    ...line.refs.map(String),
    ...line.ranges.map(([start, end]) => `${start}–${end}`),
  ];
  const references = citations.length > 0 ? `${citations.join(", ")} · ` : "";
  reason.textContent = `${references}${line.ruleLabel}`;

  row.append(number, formula, reason);
  return row;
}

function createProofSystemDetails() {
  const details = document.createElement("details");
  details.className = "proof-system";

  const summary = document.createElement("summary");
  summary.textContent = "证明系统";

  const intro = document.createElement("p");
  intro.textContent =
    "直言命题先译成一阶公式；证明只使用标准的引入、消去规则。";

  const rules = [
    "A：∀x(S(x) → P(x))；E：∀x(S(x) → ¬P(x))。",
    "I：∃x(S(x) ∧ P(x))；O：∃x(S(x) ∧ ¬P(x))。",
    "量词规则：全称引入、全称消去、存在引入、存在消去。",
    "联结词规则：条件、合取、否定的引入与消去，以及爆炸律。",
    "∀I 使用任意名字；∃E 使用只在该子证明中出现的新名字。",
  ];
  const list = document.createElement("ul");
  for (const copy of rules) {
    const item = document.createElement("li");
    item.textContent = copy;
    list.append(item);
  }

  const source = document.createElement("p");
  source.className = "proof-system__source";
  source.append("规则约定：");
  const link = document.createElement("a");
  link.href = "https://forallx.openlogicproject.org/html/Ch36.html";
  link.target = "_blank";
  link.rel = "noreferrer";
  link.textContent = "Open Logic Project《forall x: Calgary》";
  source.append(link, "。");

  details.append(summary, intro, list, source);
  return details;
}

function renderProofAnalysis(proof) {
  elements.analysisTitle.textContent = "Fitch 证明";

  const intro = document.createElement("p");
  intro.className = "analysis-intro";
  intro.textContent = `下列是一份较短的一阶 Fitch 证明，共 ${proof.lines.length} 行。`;

  const proofBlock = document.createElement("div");
  proofBlock.className = "fitch-proof";
  proofBlock.setAttribute("role", "list");
  proofBlock.setAttribute("aria-label", "Fitch 形式证明");

  const appendNodes = (parent, nodes) => {
    for (const node of nodes) {
      if (node.kind === "line") {
        parent.append(createProofLine(node.line));
        continue;
      }
      const subproof = document.createElement("div");
      subproof.className = "fitch-subproof";
      subproof.setAttribute("role", "group");
      subproof.setAttribute("aria-label", "Fitch 子证明");
      appendNodes(subproof, node.children);
      parent.append(subproof);
    }
  };
  appendNodes(proofBlock, nestProofLines(proof.lines));

  elements.analysisContent.replaceChildren(
    intro,
    proofBlock,
    createProofSystemDetails(),
  );
}

function renderCountermodelAnalysis(description) {
  elements.analysisTitle.textContent = "反例模型";

  const intro = document.createElement("p");
  intro.className = "analysis-intro";
  intro.textContent = "下列有限模型使每条前提为真，而结论为假。";

  const fragments = [intro];

  if (state.displayMode === "letters") {
    const mapping = document.createElement("p");
    mapping.className = "countermodel-mapping";
    mapping.textContent = `词项替换：${state.challenge.terms
      .map((term, index) => `${LETTER_TERMS[index]}＝${term}`)
      .join("，")}`;
    fragments.push(mapping);
  }

  const domain = document.createElement("p");
  domain.className = "countermodel-domain";
  domain.innerHTML = `<strong>论域</strong>：{${description.domain.join("，")}}`;
  fragments.push(domain);

  const objects = document.createElement("dl");
  objects.className = "countermodel-objects";
  for (const object of description.objects) {
    const row = document.createElement("div");
    const name = document.createElement("dt");
    name.textContent = object.name;
    const copy = document.createElement("dd");
    copy.textContent = object.description;
    row.append(name, copy);
    objects.append(row);
  }
  fragments.push(objects);

  const checksTitle = document.createElement("h4");
  checksTitle.textContent = "逐项核对";
  fragments.push(checksTitle);

  const checks = document.createElement("ol");
  checks.className = "countermodel-checks";
  for (const check of description.checks) {
    const item = document.createElement("li");
    if (check.kind === "conclusion") {
      item.classList.add("countermodel-check--conclusion");
    }

    const status = document.createElement("span");
    status.className = "countermodel-check__status";
    status.textContent =
      check.kind === "premise"
        ? `前提 ${check.index} · 真`
        : "结论 · 假";

    const formula = document.createElement("strong");
    formula.textContent = check.statementText;

    const reason = document.createElement("p");
    reason.textContent = check.reason;

    item.append(status, formula, reason);
    checks.append(item);
  }
  fragments.push(checks);

  elements.analysisContent.replaceChildren(...fragments);
}

function renderPostAnalysis() {
  if (!state.analysis) return;
  if (state.analysis.kind === "proof") {
    renderProofAnalysis(state.analysis.proof);
  } else {
    renderCountermodelAnalysis(state.analysis.description);
  }
}

function renderFeedbackDetails() {
  if (!state.submitted) return;

  const follows = state.challenge.follows;
  elements.correctJudgment.textContent = follows ? "是，能够推出" : "否，不能推出";
  elements.correctConclusion.textContent = formatForCurrentMode(state.challenge.conclusion);
  renderPostAnalysis();
}

function renderCurrentChallenge() {
  if (!state.challenge) return;
  renderPremises();
  renderConclusion();
  renderFeedbackDetails();
}

function resetJudgmentOptions() {
  for (const label of elements.judgmentOptions.querySelectorAll(".judgment-option")) {
    const input = label.querySelector("input");
    input.checked = false;
    input.disabled = false;
    label.classList.remove(
      "judgment-option--selected",
      "judgment-option--correct",
      "judgment-option--wrong",
    );
  }
}

function beginChallenge() {
  const previousSignature = state.challenge?.signature ?? "";
  state.challenge = generateChallenge(Math.random, previousSignature);
  state.questionNumber += 1;
  state.submitted = false;
  state.analysis = null;

  elements.emptyState.hidden = true;
  elements.question.hidden = false;
  elements.feedback.hidden = true;
  elements.feedback.className = "feedback";
  elements.questionNumber.textContent = String(state.questionNumber).padStart(2, "0");
  elements.next.textContent = "换一题";

  resetJudgmentOptions();
  renderCurrentChallenge();
  syncSubmitState();
  startTimer();

  elements.liveRegion.textContent = `第 ${state.questionNumber} 题已准备好，${state.challenge.premises.length} 个前提和一个待判断结论。`;
  elements.premises.closest("section").focus();
}

function markJudgmentOptions(selected) {
  for (const label of elements.judgmentOptions.querySelectorAll(".judgment-option")) {
    const input = label.querySelector("input");
    const answer = input.value === "true";
    input.disabled = true;

    if (answer === state.challenge.follows) {
      label.classList.add("judgment-option--correct");
    } else if (answer === selected) {
      label.classList.add("judgment-option--wrong");
    }
  }
}

function submitAnswer() {
  if (state.submitted) return;

  const selected = selectedAnswer();
  if (selected === null) {
    elements.liveRegion.textContent = "请先判断这个结论能否推出。";
    return;
  }

  const exact = selected === state.challenge.follows;
  const elapsed = stopTimer();

  state.submitted = true;
  state.total += 1;
  if (exact) state.correct += 1;

  if (state.challenge.follows) {
    state.analysis = {
      kind: "proof",
      proof: buildFitchProof(
        state.challenge.premises,
        state.challenge.conclusion,
        state.challenge.terms.length,
      ),
    };
  } else {
    const model = findCountermodel(
      state.challenge.premises,
      state.challenge.conclusion,
      state.challenge.terms.length,
    );
    if (!model) {
      throw new Error("语义判定为无效，但没有找到反例模型。");
    }
    state.analysis = {
      kind: "countermodel",
      description: describeCountermodel(
        model,
        state.challenge.premises,
        state.challenge.conclusion,
        state.challenge.terms,
      ),
    };
  }

  markJudgmentOptions(selected);
  updateStats();

  elements.feedback.hidden = false;
  elements.feedback.classList.add(exact ? "feedback--success" : "feedback--retry");
  elements.feedbackTitle.textContent = exact ? "回答正确" : "回答错误";
  elements.feedbackSummary.textContent = `本题用时 ${formatDuration(
    elapsed,
  )}；当前正确率 ${Math.round((state.correct / state.total) * 100)}%。`;
  elements.next.textContent = "下一题";
  renderFeedbackDetails();
  syncSubmitState();

  elements.liveRegion.textContent = `${elements.feedbackTitle.textContent}。正确答案是“${elements.correctJudgment.textContent}”。${elements.feedbackSummary.textContent}`;
  elements.feedback.scrollIntoView({ behavior: "smooth", block: "nearest" });
}

function updateDisplayMode() {
  state.displayMode = elements.letterMode.checked ? "letters" : "natural";
  const usingLetters = state.displayMode === "letters";
  elements.modeStatus.textContent = usingLetters
    ? "字母形式：使用 S、M、P 等词项和标准 AEIO 句式"
    : "自然语言：词项与等价句式随机变化";
  renderCurrentChallenge();
  elements.liveRegion.textContent = elements.modeStatus.textContent;
}

for (const input of elements.judgmentOptions.querySelectorAll("input")) {
  input.addEventListener("change", () => {
    for (const label of elements.judgmentOptions.querySelectorAll(".judgment-option")) {
      label.classList.toggle(
        "judgment-option--selected",
        label.querySelector("input").checked,
      );
    }
    syncSubmitState();
  });
}

elements.next.addEventListener("click", beginChallenge);
elements.submit.addEventListener("click", submitAnswer);
elements.letterMode.addEventListener("change", updateDisplayMode);

document.addEventListener("keydown", (event) => {
  if ((event.ctrlKey || event.metaKey) && event.key === "Enter" && !elements.submit.disabled) {
    event.preventDefault();
    submitAnswer();
  }
});

updateStats();
updateDisplayMode();
