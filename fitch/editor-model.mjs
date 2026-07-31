function replaceCitationNumbers(raw, mapper) {
  return String(raw ?? "").replace(/\d+/gu, (digits) =>
    String(mapper(Number(digits))),
  );
}

export function citationNumbers(raw) {
  return [...String(raw ?? "").matchAll(/\d+/gu)].map((match) =>
    Number(match[0]),
  );
}

export function citationReferencesLine(raw, lineNumber) {
  return citationNumbers(raw).includes(lineNumber);
}

export function shiftCitationsForAddedPremise(raw, previousPremiseCount) {
  return replaceCitationNumbers(raw, (number) =>
    number > previousPremiseCount ? number + 1 : number,
  );
}

export function shiftCitationsForRemovedPremise(raw, removedLineNumber) {
  return replaceCitationNumbers(raw, (number) =>
    number > removedLineNumber ? number - 1 : number,
  );
}

export function pathForNextLine(lines) {
  return lines.length > 0 ? [...lines.at(-1).path] : [];
}

export function makeSubproofAssumption(line, scopeId) {
  if (!line || line.isAssumption) return line;
  return {
    ...line,
    path: [...line.path, String(scopeId)],
    isAssumption: true,
    rule: "assumption",
    citations: "",
  };
}

export function moveLineToParentScope(line) {
  if (!line || line.path.length === 0) return line;
  const moved = {
    ...line,
    path: line.path.slice(0, -1),
  };
  if (line.isAssumption) {
    moved.isAssumption = false;
    moved.rule = "reiteration";
  }
  return moved;
}
