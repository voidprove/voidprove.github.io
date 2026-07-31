const IDENTIFIER_PATTERN = /^[A-Za-z](?:_\d+)?/;
const VARIABLE_PATTERN = /^[xyz](?:_\d+)?$/;
const CONSTANT_PATTERN = /^[abc](?:_\d+)?$/;
const FUNCTION_PATTERN = /^[fgh](?:_\d+)?$/;
const PROPOSITION_PATTERN = /^[pqr](?:_\d+)?$/;
const PREDICATE_PATTERN = /^[A-Z](?:_\d+)?$/;
const COMMAND_PATTERN = /^\\[A-Za-z]+/u;
const MAX_NESTING_DEPTH = 256;

const COMMAND_TOKENS = Object.freeze({
  forall: "forall",
  exists: "exists",
  not: "not",
  neg: "not",
  lnot: "not",
  and: "and",
  land: "and",
  wedge: "and",
  or: "or",
  lor: "or",
  vee: "or",
  implies: "implies",
  to: "implies",
  rightarrow: "implies",
  iff: "iff",
  leftrightarrow: "iff",
  neq: "not-equals",
  ne: "not-equals",
});

const WORD_TOKENS = Object.freeze([
  ["当且仅当", "iff"],
  ["任意", "forall"],
  ["存在", "exists"],
  ["蕴含", "implies"],
  ["且", "and"],
  ["或", "or"],
  ["非", "not"],
]);

const CHARACTER_TOKENS = Object.freeze({
  "∀": "forall",
  "∃": "exists",
  "∧": "and",
  "∨": "or",
  "¬": "not",
  "→": "implies",
  "↔": "iff",
  "=": "equals",
  "≠": "not-equals",
  "(": "left-paren",
  ")": "right-paren",
  ",": "comma",
});

const BINARY_OPERATOR_TYPES = Object.freeze(["and", "or", "implies", "iff"]);

export class FormulaSyntaxError extends SyntaxError {
  constructor(message, position, end = position + 1, code = "SYNTAX_ERROR") {
    super(message);
    this.name = "FormulaSyntaxError";
    this.code = code;
    this.position = position;
    this.end = end;
  }
}

export class SignatureError extends Error {
  constructor(warning) {
    super(
      `${warning.name} 的元数不一致：首次为 ${warning.expectedArity}，此处为 ${warning.actualArity}`,
    );
    Object.assign(this, warning, { symbolName: warning.name });
    this.name = "SignatureError";
  }
}

function syntaxError(message, token, code = "SYNTAX_ERROR") {
  return new FormulaSyntaxError(message, token.start, token.end, code);
}

function tokenize(source) {
  const tokens = [];
  let cursor = 0;

  while (cursor < source.length) {
    const character = String.fromCodePoint(source.codePointAt(cursor));
    if (/\s/u.test(character)) {
      cursor += 1;
      continue;
    }

    if (character === "\\") {
      const commandMatch = source.slice(cursor).match(COMMAND_PATTERN);
      if (!commandMatch) {
        throw new FormulaSyntaxError(
          "反斜线后必须输入命令名称",
          cursor,
          cursor + 1,
          "UNKNOWN_COMMAND",
        );
      }

      const value = commandMatch[0];
      const commandName = value.slice(1);
      const type = Object.prototype.hasOwnProperty.call(
        COMMAND_TOKENS,
        commandName,
      )
        ? COMMAND_TOKENS[commandName]
        : undefined;
      if (!type) {
        throw new FormulaSyntaxError(
          `无法识别命令“${value}”`,
          cursor,
          cursor + value.length,
          "UNKNOWN_COMMAND",
        );
      }

      tokens.push({
        type,
        value,
        start: cursor,
        end: cursor + value.length,
      });
      cursor += value.length;
      continue;
    }

    let matchedWord = false;
    for (const [word, type] of WORD_TOKENS) {
      if (!source.startsWith(word, cursor)) continue;
      tokens.push({ type, value: word, start: cursor, end: cursor + word.length });
      cursor += word.length;
      matchedWord = true;
      break;
    }
    if (matchedWord) continue;

    const characterType = CHARACTER_TOKENS[character];
    if (characterType) {
      tokens.push({
        type: characterType,
        value: character,
        start: cursor,
        end: cursor + character.length,
      });
      cursor += character.length;
      continue;
    }

    const identifierMatch = source.slice(cursor).match(IDENTIFIER_PATTERN);
    if (identifierMatch) {
      const value = identifierMatch[0];
      tokens.push({
        type: "identifier",
        value,
        start: cursor,
        end: cursor + value.length,
      });
      cursor += value.length;
      continue;
    }

    throw new FormulaSyntaxError(
      `无法识别字符“${character}”`,
      cursor,
      cursor + character.length,
      "UNKNOWN_CHARACTER",
    );
  }

  tokens.push({
    type: "end",
    value: "",
    start: source.length,
    end: source.length,
  });
  return tokens;
}

function isVariableName(name) {
  return VARIABLE_PATTERN.test(name);
}

function isConstantName(name) {
  return CONSTANT_PATTERN.test(name);
}

function isFunctionName(name) {
  return FUNCTION_PATTERN.test(name);
}

function isPropositionName(name) {
  return PROPOSITION_PATTERN.test(name);
}

function isPredicateName(name) {
  return PREDICATE_PATTERN.test(name);
}

class Parser {
  constructor(source) {
    if (typeof source !== "string") {
      throw new TypeError("公式必须是字符串");
    }
    this.source = source;
    this.tokens = tokenize(source);
    this.cursor = 0;
    this.formulaNestingDepth = 0;
    this.termNestingDepth = 0;
  }

  current() {
    return this.tokens[this.cursor];
  }

  previous() {
    return this.tokens[this.cursor - 1];
  }

  at(type) {
    return this.current().type === type;
  }

  consume(type, message, code = "UNEXPECTED_TOKEN") {
    const token = this.current();
    if (token.type !== type) {
      throw syntaxError(message, token, code);
    }
    this.cursor += 1;
    return token;
  }

  match(type) {
    if (!this.at(type)) return false;
    this.cursor += 1;
    return true;
  }

  withFormulaNesting(token, callback) {
    if (this.formulaNestingDepth >= MAX_NESTING_DEPTH) {
      throw syntaxError(
        `公式嵌套不能超过 ${MAX_NESTING_DEPTH} 层`,
        token,
        "NESTING_TOO_DEEP",
      );
    }
    this.formulaNestingDepth += 1;
    try {
      return callback();
    } finally {
      this.formulaNestingDepth -= 1;
    }
  }

  withTermNesting(token, callback) {
    if (this.termNestingDepth >= MAX_NESTING_DEPTH) {
      throw syntaxError(
        `项的嵌套不能超过 ${MAX_NESTING_DEPTH} 层`,
        token,
        "NESTING_TOO_DEEP",
      );
    }
    this.termNestingDepth += 1;
    try {
      return callback();
    } finally {
      this.termNestingDepth -= 1;
    }
  }

  parseFormulaRoot() {
    if (this.at("end")) {
      throw syntaxError("请输入公式", this.current(), "EMPTY_FORMULA");
    }
    const formula = this.parseFormulaExpression();
    if (!this.at("end")) {
      throw syntaxError(
        `公式末尾有多余内容“${this.current().value}”`,
        this.current(),
        "TRAILING_INPUT",
      );
    }
    return formula;
  }

  parseTermRoot() {
    if (this.at("end")) {
      throw syntaxError("请输入项", this.current(), "EMPTY_TERM");
    }
    const term = this.parseTermNode();
    if (!this.at("end")) {
      throw syntaxError(
        `项末尾有多余内容“${this.current().value}”`,
        this.current(),
        "TRAILING_INPUT",
      );
    }
    return term;
  }

  parseFormulaExpression() {
    const left = this.parseUnaryFormula();
    if (!BINARY_OPERATOR_TYPES.includes(this.current().type)) return left;

    const operatorToken = this.current();
    this.cursor += 1;
    const right = this.parseUnaryFormula();

    if (BINARY_OPERATOR_TYPES.includes(this.current().type)) {
      throw syntaxError(
        "同一层不能出现多个二元联结词；请用括号明确分组",
        this.current(),
        "MISSING_BINARY_PARENTHESES",
      );
    }

    return {
      kind: "binary",
      operator: operatorToken.type,
      left,
      right,
    };
  }

  parseUnaryFormula() {
    if (this.at("not")) {
      const negationToken = this.current();
      this.cursor += 1;
      return {
        kind: "not",
        value: this.withFormulaNesting(negationToken, () =>
          this.parseUnaryFormula(),
        ),
      };
    }

    if (this.at("forall") || this.at("exists")) {
      const quantifierToken = this.current();
      this.cursor += 1;
      const variableToken = this.consume(
        "identifier",
        "量词后必须有变量",
        "EXPECTED_VARIABLE",
      );
      if (!isVariableName(variableToken.value)) {
        throw syntaxError(
          `“${variableToken.value}”不是变量；变量须使用 x、y、z`,
          variableToken,
          "INVALID_VARIABLE",
        );
      }
      if (this.at("end")) {
        throw syntaxError(
          "量词后缺少公式",
          this.current(),
          "EXPECTED_FORMULA",
        );
      }
      return {
        kind: "quantifier",
        quantifier: quantifierToken.type,
        variable: variableToken.value,
        body: this.withFormulaNesting(quantifierToken, () =>
          this.parseUnaryFormula(),
        ),
      };
    }

    return this.parseAtomicFormula();
  }

  parseAtomicFormula() {
    if (this.at("left-paren")) {
      // Parenthesized terms are accepted on the left of equality. Because the
      // same opening parenthesis may instead group a formula, try the term
      // reading first and restore the cursor unless an equality follows it.
      const savedCursor = this.cursor;
      try {
        const left = this.parseTermNode();
        const equalityToken = this.current();
        if (this.match("equals") || this.match("not-equals")) {
          const equality = {
            kind: "equality",
            left,
            right: this.parseTermNode(),
          };
          return equalityToken.type === "not-equals"
            ? { kind: "not", value: equality }
            : equality;
        }
      } catch (error) {
        if (!(error instanceof FormulaSyntaxError)) throw error;
      }
      this.cursor = savedCursor;
      const openToken = this.consume("left-paren", "缺少左括号 (");
      const formula = this.withFormulaNesting(openToken, () =>
        this.parseFormulaExpression(),
      );
      this.consume(
        "right-paren",
        "缺少右括号 )",
        "UNMATCHED_PARENTHESIS",
      );
      return formula;
    }

    const token = this.current();
    if (token.type !== "identifier") {
      throw syntaxError("此处应为公式", token, "EXPECTED_FORMULA");
    }

    if (isPropositionName(token.value)) {
      this.cursor += 1;
      if (this.at("left-paren")) {
        throw syntaxError(
          `命题常项“${token.value}”不能带参数`,
          this.current(),
          "PROPOSITION_WITH_ARGUMENTS",
        );
      }
      return { kind: "proposition", name: token.value };
    }

    if (isPredicateName(token.value)) {
      this.cursor += 1;
      const open = this.current();
      if (open.type !== "left-paren") {
        throw syntaxError(
          `谓词“${token.value}”后必须紧接参数括号`,
          open,
          "PREDICATE_ARGUMENTS_REQUIRED",
        );
      }
      if (token.end !== open.start) {
        throw new FormulaSyntaxError(
          `谓词“${token.value}”和左括号之间不能有空格`,
          token.end,
          open.start,
          "APPLICATION_WHITESPACE",
        );
      }
      return {
        kind: "predicate",
        name: token.value,
        args: this.parseArgumentList("谓词"),
      };
    }

    if (
      isVariableName(token.value) ||
      isConstantName(token.value) ||
      isFunctionName(token.value)
    ) {
      const left = this.parseTermNode();
      const equalityToken = this.current();
      if (!this.match("equals") && !this.match("not-equals")) {
        throw syntaxError(
          "项本身不是公式；此处应有 = 或 ≠",
          equalityToken,
          "EXPECTED_EQUALITY",
        );
      }
      const equality = {
        kind: "equality",
        left,
        right: this.parseTermNode(),
      };
      return equalityToken.type === "not-equals"
        ? { kind: "not", value: equality }
        : equality;
    }

    throw syntaxError(
      `“${token.value}”不能出现在公式中`,
      token,
      "INVALID_IDENTIFIER",
    );
  }

  parseArgumentList(label) {
    this.consume("left-paren", `${label}后缺少左括号 (`);
    if (this.at("right-paren")) {
      throw syntaxError(
        `${label}至少需要一个参数`,
        this.current(),
        "EMPTY_ARGUMENT_LIST",
      );
    }

    const args = [this.parseTermNode()];
    while (this.match("comma")) {
      args.push(this.parseTermNode());
    }
    this.consume(
      "right-paren",
      `${label}的参数列表缺少右括号 )`,
      "UNMATCHED_PARENTHESIS",
    );
    return args;
  }

  parseTermNode() {
    if (this.at("left-paren")) {
      const openToken = this.consume("left-paren", "项缺少左括号 (");
      const term = this.withTermNesting(openToken, () => this.parseTermNode());
      this.consume(
        "right-paren",
        "项缺少右括号 )",
        "UNMATCHED_PARENTHESIS",
      );
      return term;
    }

    const token = this.consume(
      "identifier",
      "此处应为项",
      "EXPECTED_TERM",
    );

    if (isVariableName(token.value)) {
      return { kind: "variable", name: token.value };
    }
    if (isConstantName(token.value)) {
      return { kind: "constant", name: token.value };
    }
    if (isFunctionName(token.value)) {
      const open = this.current();
      if (open.type !== "left-paren") {
        throw syntaxError(
          `函数“${token.value}”后必须紧接参数括号`,
          open,
          "FUNCTION_ARGUMENTS_REQUIRED",
        );
      }
      if (token.end !== open.start) {
        throw new FormulaSyntaxError(
          `函数“${token.value}”和左括号之间不能有空格`,
          token.end,
          open.start,
          "APPLICATION_WHITESPACE",
        );
      }
      return {
        kind: "function",
        name: token.value,
        args: this.withTermNesting(token, () => this.parseArgumentList("函数")),
      };
    }

    throw syntaxError(
      `“${token.value}”不是项；项须使用变量 x/y/z、常项 a/b/c 或函数 f/g/h`,
      token,
      "INVALID_TERM_IDENTIFIER",
    );
  }
}

export function parseFormula(source) {
  return new Parser(source).parseFormulaRoot();
}

export function parseTerm(source) {
  return new Parser(source).parseTermRoot();
}

function cloneTerm(term) {
  if (term.kind !== "function") return { ...term };
  return { ...term, args: term.args.map(cloneTerm) };
}

function cloneFormula(formula) {
  switch (formula.kind) {
    case "proposition":
      return { ...formula };
    case "predicate":
      return { ...formula, args: formula.args.map(cloneTerm) };
    case "equality":
      return {
        ...formula,
        left: cloneTerm(formula.left),
        right: cloneTerm(formula.right),
      };
    case "not":
      return { ...formula, value: cloneFormula(formula.value) };
    case "binary":
      return {
        ...formula,
        left: cloneFormula(formula.left),
        right: cloneFormula(formula.right),
      };
    case "quantifier":
      return { ...formula, body: cloneFormula(formula.body) };
    default:
      throw new TypeError(`未知公式节点：${formula?.kind}`);
  }
}

export function termEquals(left, right) {
  if (!left || !right || left.kind !== right.kind || left.name !== right.name) {
    return false;
  }
  if (left.kind !== "function") return true;
  return (
    left.args.length === right.args.length &&
    left.args.every((argument, index) => termEquals(argument, right.args[index]))
  );
}

export function formulaEquals(left, right) {
  if (!left || !right || left.kind !== right.kind) return false;
  switch (left.kind) {
    case "proposition":
      return left.name === right.name;
    case "predicate":
      return (
        left.name === right.name &&
        left.args.length === right.args.length &&
        left.args.every((argument, index) =>
          termEquals(argument, right.args[index]),
        )
      );
    case "equality":
      return termEquals(left.left, right.left) && termEquals(left.right, right.right);
    case "not":
      return formulaEquals(left.value, right.value);
    case "binary":
      return (
        left.operator === right.operator &&
        formulaEquals(left.left, right.left) &&
        formulaEquals(left.right, right.right)
      );
    case "quantifier":
      return (
        left.quantifier === right.quantifier &&
        left.variable === right.variable &&
        formulaEquals(left.body, right.body)
      );
    default:
      return false;
  }
}

function boundLevel(name, environment, side) {
  for (let index = environment.length - 1; index >= 0; index -= 1) {
    if (environment[index][side] === name) return index;
  }
  return -1;
}

function alphaTermEquals(left, right, environment) {
  if (!left || !right || left.kind !== right.kind) return false;
  if (left.kind === "variable") {
    const leftLevel = boundLevel(left.name, environment, "left");
    const rightLevel = boundLevel(right.name, environment, "right");
    if (leftLevel >= 0 || rightLevel >= 0) return leftLevel === rightLevel;
    return left.name === right.name;
  }
  if (left.kind === "constant") return left.name === right.name;
  return (
    left.name === right.name &&
    left.args.length === right.args.length &&
    left.args.every((argument, index) =>
      alphaTermEquals(argument, right.args[index], environment),
    )
  );
}

function alphaFormulaEquals(left, right, environment) {
  if (!left || !right || left.kind !== right.kind) return false;
  switch (left.kind) {
    case "proposition":
      return left.name === right.name;
    case "predicate":
      return (
        left.name === right.name &&
        left.args.length === right.args.length &&
        left.args.every((argument, index) =>
          alphaTermEquals(argument, right.args[index], environment),
        )
      );
    case "equality":
      return (
        alphaTermEquals(left.left, right.left, environment) &&
        alphaTermEquals(left.right, right.right, environment)
      );
    case "not":
      return alphaFormulaEquals(left.value, right.value, environment);
    case "binary":
      return (
        left.operator === right.operator &&
        alphaFormulaEquals(left.left, right.left, environment) &&
        alphaFormulaEquals(left.right, right.right, environment)
      );
    case "quantifier":
      return (
        left.quantifier === right.quantifier &&
        alphaFormulaEquals(left.body, right.body, [
          ...environment,
          { left: left.variable, right: right.variable },
        ])
      );
    default:
      return false;
  }
}

export function alphaEquivalent(left, right) {
  return alphaFormulaEquals(left, right, []);
}

function addTermVariables(term, target) {
  if (term.kind === "variable") target.add(term.name);
  if (term.kind === "function") {
    term.args.forEach((argument) => addTermVariables(argument, target));
  }
}

function addFreeVariables(formula, target, bound) {
  const visitTerm = (term) => {
    if (term.kind === "variable" && !bound.includes(term.name)) {
      target.add(term.name);
    }
    if (term.kind === "function") term.args.forEach(visitTerm);
  };

  switch (formula.kind) {
    case "proposition":
      break;
    case "predicate":
      formula.args.forEach(visitTerm);
      break;
    case "equality":
      visitTerm(formula.left);
      visitTerm(formula.right);
      break;
    case "not":
      addFreeVariables(formula.value, target, bound);
      break;
    case "binary":
      addFreeVariables(formula.left, target, bound);
      addFreeVariables(formula.right, target, bound);
      break;
    case "quantifier":
      addFreeVariables(formula.body, target, [...bound, formula.variable]);
      break;
    default:
      throw new TypeError(`未知公式节点：${formula?.kind}`);
  }
}

export function freeVariables(formula) {
  const result = new Set();
  addFreeVariables(formula, result, []);
  return result;
}

function collectTermConstants(term, target) {
  if (term.kind === "constant") target.add(term.name);
  if (term.kind === "function") {
    term.args.forEach((argument) => collectTermConstants(argument, target));
  }
}

export function collectConstants(formula) {
  const result = new Set();
  walkFormula(formula, {
    term(term) {
      collectTermConstants(term, result);
    },
  });
  return result;
}

function walkTerm(term, visitor) {
  visitor.term?.(term);
  if (term.kind === "function") {
    visitor.function?.(term);
    term.args.forEach((argument) => walkTerm(argument, visitor));
  }
}

function walkFormula(formula, visitor) {
  visitor.formula?.(formula);
  switch (formula.kind) {
    case "proposition":
      visitor.proposition?.(formula);
      break;
    case "predicate":
      visitor.predicate?.(formula);
      formula.args.forEach((argument) => walkTerm(argument, visitor));
      break;
    case "equality":
      walkTerm(formula.left, visitor);
      walkTerm(formula.right, visitor);
      break;
    case "not":
      walkFormula(formula.value, visitor);
      break;
    case "binary":
      walkFormula(formula.left, visitor);
      walkFormula(formula.right, visitor);
      break;
    case "quantifier":
      visitor.variable?.(formula.variable, true);
      walkFormula(formula.body, visitor);
      break;
    default:
      throw new TypeError(`未知公式节点：${formula?.kind}`);
  }
}

export function collectNames(formula) {
  const result = {
    variables: new Set(),
    constants: new Set(),
    functions: new Set(),
    predicates: new Set(),
    propositions: new Set(),
  };
  walkFormula(formula, {
    variable(name) {
      result.variables.add(name);
    },
    term(term) {
      if (term.kind === "variable") result.variables.add(term.name);
      if (term.kind === "constant") result.constants.add(term.name);
    },
    function(term) {
      result.functions.add(term.name);
    },
    predicate(node) {
      result.predicates.add(node.name);
    },
    proposition(node) {
      result.propositions.add(node.name);
    },
  });
  return result;
}

function termContainsVariable(term, variableName) {
  if (term.kind === "variable") return term.name === variableName;
  return (
    term.kind === "function" &&
    term.args.some((argument) => termContainsVariable(argument, variableName))
  );
}

function hasFreeOccurrence(formula, variableName, bound = []) {
  if (bound.includes(variableName)) return false;
  switch (formula.kind) {
    case "proposition":
      return false;
    case "predicate":
      return formula.args.some((term) => termContainsVariable(term, variableName));
    case "equality":
      return (
        termContainsVariable(formula.left, variableName) ||
        termContainsVariable(formula.right, variableName)
      );
    case "not":
      return hasFreeOccurrence(formula.value, variableName, bound);
    case "binary":
      return (
        hasFreeOccurrence(formula.left, variableName, bound) ||
        hasFreeOccurrence(formula.right, variableName, bound)
      );
    case "quantifier":
      return hasFreeOccurrence(formula.body, variableName, [
        ...bound,
        formula.variable,
      ]);
    default:
      return false;
  }
}

function renameTermVariable(term, oldName, newName) {
  if (term.kind === "variable") {
    return term.name === oldName ? { ...term, name: newName } : { ...term };
  }
  if (term.kind === "constant") return { ...term };
  return {
    ...term,
    args: term.args.map((argument) =>
      renameTermVariable(argument, oldName, newName),
    ),
  };
}

function renameBoundOccurrences(formula, oldName, newName) {
  switch (formula.kind) {
    case "proposition":
      return { ...formula };
    case "predicate":
      return {
        ...formula,
        args: formula.args.map((term) =>
          renameTermVariable(term, oldName, newName),
        ),
      };
    case "equality":
      return {
        ...formula,
        left: renameTermVariable(formula.left, oldName, newName),
        right: renameTermVariable(formula.right, oldName, newName),
      };
    case "not":
      return {
        ...formula,
        value: renameBoundOccurrences(formula.value, oldName, newName),
      };
    case "binary":
      return {
        ...formula,
        left: renameBoundOccurrences(formula.left, oldName, newName),
        right: renameBoundOccurrences(formula.right, oldName, newName),
      };
    case "quantifier":
      if (formula.variable === oldName) return cloneFormula(formula);
      return {
        ...formula,
        body: renameBoundOccurrences(formula.body, oldName, newName),
      };
    default:
      throw new TypeError(`未知公式节点：${formula?.kind}`);
  }
}

function allVariableNames(formula, replacement) {
  const names = collectNames(formula).variables;
  addTermVariables(replacement, names);
  return names;
}

function freshVariable(usedNames) {
  for (const base of ["x", "y", "z"]) {
    if (!usedNames.has(base)) return base;
  }
  for (let subscript = 1; ; subscript += 1) {
    for (const base of ["x", "y", "z"]) {
      const candidate = `${base}_${subscript}`;
      if (!usedNames.has(candidate)) return candidate;
    }
  }
}

function substituteTerm(term, variableName, replacement) {
  if (term.kind === "variable" && term.name === variableName) {
    return cloneTerm(replacement);
  }
  if (term.kind !== "function") return { ...term };
  return {
    ...term,
    args: term.args.map((argument) =>
      substituteTerm(argument, variableName, replacement),
    ),
  };
}

export function substitute(formula, variableName, replacement) {
  if (!isVariableName(variableName)) {
    throw new TypeError("被替换名称必须是 x、y、z 之一（可带数字下标）");
  }
  if (!replacement || !["variable", "constant", "function"].includes(replacement.kind)) {
    throw new TypeError("替换对象必须是项");
  }

  const replacementVariables = new Set();
  addTermVariables(replacement, replacementVariables);

  const visit = (node) => {
    switch (node.kind) {
      case "proposition":
        return { ...node };
      case "predicate":
        return {
          ...node,
          args: node.args.map((term) =>
            substituteTerm(term, variableName, replacement),
          ),
        };
      case "equality":
        return {
          ...node,
          left: substituteTerm(node.left, variableName, replacement),
          right: substituteTerm(node.right, variableName, replacement),
        };
      case "not":
        return { ...node, value: visit(node.value) };
      case "binary":
        return { ...node, left: visit(node.left), right: visit(node.right) };
      case "quantifier": {
        if (node.variable === variableName) return cloneFormula(node);
        if (
          replacementVariables.has(node.variable) &&
          hasFreeOccurrence(node.body, variableName)
        ) {
          const fresh = freshVariable(allVariableNames(node, replacement));
          const renamedBody = renameBoundOccurrences(
            node.body,
            node.variable,
            fresh,
          );
          return { ...node, variable: fresh, body: visit(renamedBody) };
        }
        return { ...node, body: visit(node.body) };
      }
      default:
        throw new TypeError(`未知公式节点：${node?.kind}`);
    }
  };

  return visit(formula);
}

function candidateTermContainsBoundVariable(term, environment) {
  if (term.kind === "variable") {
    return boundLevel(term.name, environment, "right") >= 0;
  }
  return (
    term.kind === "function" &&
    term.args.some((argument) =>
      candidateTermContainsBoundVariable(argument, environment),
    )
  );
}

export function matchSubstitutionInstance(body, variableName, candidate) {
  let inferred;
  let sawOccurrence = false;

  const matchTerm = (sourceTerm, candidateTerm, environment) => {
    if (sourceTerm.kind === "variable") {
      const sourceLevel = boundLevel(sourceTerm.name, environment, "left");
      if (sourceLevel >= 0) {
        return (
          candidateTerm.kind === "variable" &&
          boundLevel(candidateTerm.name, environment, "right") === sourceLevel
        );
      }
      if (sourceTerm.name === variableName) {
        sawOccurrence = true;
        if (candidateTermContainsBoundVariable(candidateTerm, environment)) {
          return false;
        }
        if (inferred === undefined) inferred = cloneTerm(candidateTerm);
        return termEquals(inferred, candidateTerm);
      }
      return (
        candidateTerm.kind === "variable" &&
        boundLevel(candidateTerm.name, environment, "right") < 0 &&
        candidateTerm.name === sourceTerm.name
      );
    }
    if (sourceTerm.kind === "constant") {
      return candidateTerm.kind === "constant" && sourceTerm.name === candidateTerm.name;
    }
    return (
      candidateTerm.kind === "function" &&
      sourceTerm.name === candidateTerm.name &&
      sourceTerm.args.length === candidateTerm.args.length &&
      sourceTerm.args.every((argument, index) =>
        matchTerm(argument, candidateTerm.args[index], environment),
      )
    );
  };

  const matchFormula = (sourceFormula, candidateFormula, environment) => {
    if (sourceFormula.kind !== candidateFormula.kind) return false;
    switch (sourceFormula.kind) {
      case "proposition":
        return sourceFormula.name === candidateFormula.name;
      case "predicate":
        return (
          sourceFormula.name === candidateFormula.name &&
          sourceFormula.args.length === candidateFormula.args.length &&
          sourceFormula.args.every((argument, index) =>
            matchTerm(argument, candidateFormula.args[index], environment),
          )
        );
      case "equality":
        return (
          matchTerm(sourceFormula.left, candidateFormula.left, environment) &&
          matchTerm(sourceFormula.right, candidateFormula.right, environment)
        );
      case "not":
        return matchFormula(sourceFormula.value, candidateFormula.value, environment);
      case "binary":
        return (
          sourceFormula.operator === candidateFormula.operator &&
          matchFormula(sourceFormula.left, candidateFormula.left, environment) &&
          matchFormula(sourceFormula.right, candidateFormula.right, environment)
        );
      case "quantifier":
        return (
          sourceFormula.quantifier === candidateFormula.quantifier &&
          matchFormula(sourceFormula.body, candidateFormula.body, [
            ...environment,
            { left: sourceFormula.variable, right: candidateFormula.variable },
          ])
        );
      default:
        return false;
    }
  };

  const structurallyMatches = matchFormula(body, candidate, []);
  if (!structurallyMatches) return { matches: false, term: null };
  if (!sawOccurrence) {
    return { matches: alphaEquivalent(body, candidate), term: null };
  }
  const substituted = substitute(body, variableName, inferred);
  return {
    matches: alphaEquivalent(substituted, candidate),
    term: inferred,
  };
}

export function collectSignatureEntries(formula) {
  const entries = [];
  walkFormula(formula, {
    proposition(node) {
      entries.push({ kind: "predicate", name: node.name, arity: 0 });
    },
    predicate(node) {
      entries.push({ kind: "predicate", name: node.name, arity: node.args.length });
    },
    function(node) {
      entries.push({ kind: "function", name: node.name, arity: node.args.length });
    },
  });
  return entries;
}

export function validateSignatures(formulas) {
  const predicates = new Map();
  const functions = new Map();
  const warnings = [];

  formulas.forEach((formula, formulaIndex) => {
    collectSignatureEntries(formula).forEach((entry) => {
      const signature = entry.kind === "predicate" ? predicates : functions;
      if (!signature.has(entry.name)) {
        signature.set(entry.name, entry.arity);
        return;
      }
      const expectedArity = signature.get(entry.name);
      if (expectedArity === entry.arity) return;
      warnings.push({
        code: "INCONSISTENT_ARITY",
        formulaIndex,
        kind: entry.kind,
        name: entry.name,
        expectedArity,
        actualArity: entry.arity,
      });
    });
  });

  return {
    valid: warnings.length === 0,
    warnings,
    predicates,
    functions,
  };
}

const OPERATOR_SYMBOL = Object.freeze({
  and: "∧",
  or: "∨",
  implies: "→",
  iff: "↔",
});

export function formatTerm(term) {
  switch (term.kind) {
    case "variable":
    case "constant":
      return term.name;
    case "function":
      return `${term.name}(${term.args.map(formatTerm).join(", ")})`;
    default:
      throw new TypeError(`未知项节点：${term?.kind}`);
  }
}

function formatNestedFormula(formula) {
  const text = formatFormulaNode(formula);
  return formula.kind === "binary" ? `(${text})` : text;
}

function formatFormulaNode(formula) {
  switch (formula.kind) {
    case "proposition":
      return formula.name;
    case "predicate":
      return `${formula.name}(${formula.args.map(formatTerm).join(", ")})`;
    case "equality":
      return `${formatTerm(formula.left)} = ${formatTerm(formula.right)}`;
    case "not":
      return `¬${formatNestedFormula(formula.value)}`;
    case "quantifier": {
      const symbol = formula.quantifier === "forall" ? "∀" : "∃";
      const separator = formula.body.kind === "binary" ? "" : " ";
      return `${symbol}${formula.variable}${separator}${formatNestedFormula(formula.body)}`;
    }
    case "binary":
      return `${formatNestedFormula(formula.left)} ${
        OPERATOR_SYMBOL[formula.operator]
      } ${formatNestedFormula(formula.right)}`;
    default:
      throw new TypeError(`未知公式节点：${formula?.kind}`);
  }
}

export function formatFormula(formula) {
  return formatFormulaNode(formula);
}
