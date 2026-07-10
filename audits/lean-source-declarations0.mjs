export function stripLeanCommentsAndStrings0(source) {
  let out = '';
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let string = false;
  while (index < source.length) {
    const here = source[index];
    const next = source[index + 1] ?? '';
    if (lineComment) {
      if (here === '\n') {
        lineComment = false;
        out += '\n';
      } else out += ' ';
      index += 1;
      continue;
    }
    if (blockDepth > 0) {
      if (here === '/' && next === '-') {
        blockDepth += 1;
        out += '  ';
        index += 2;
      } else if (here === '-' && next === '/') {
        blockDepth -= 1;
        out += '  ';
        index += 2;
      } else {
        out += here === '\n' ? '\n' : ' ';
        index += 1;
      }
      continue;
    }
    if (string) {
      if (here === '\\') {
        out += '  ';
        index += Math.min(2, source.length - index);
      } else if (here === '"') {
        string = false;
        out += ' ';
        index += 1;
      } else {
        out += here === '\n' ? '\n' : ' ';
        index += 1;
      }
      continue;
    }
    if (here === '-' && next === '-') {
      lineComment = true;
      out += '  ';
      index += 2;
    } else if (here === '/' && next === '-') {
      blockDepth = 1;
      out += '  ';
      index += 2;
    } else if (here === '"') {
      string = true;
      out += ' ';
      index += 1;
    } else {
      out += here;
      index += 1;
    }
  }
  return out;
}

export function explicitLeanDeclarationHeads0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(/^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:protected|noncomputable)[ \t]+)*(def|theorem|inductive|structure|abbrev)[ \t]+(«[^»\n]+»|[^\s({:]+)/gmu)]
    .map((match) => ({ kind: match[1], name: match[2], index: match.index }));
}

export function hasLeanAssumptionDeclaration0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return /^\s*(?:@\[[^\]\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:axiom|constant|opaque)\b/mu.test(stripped);
}

export function hasPrivateLeanDeclaration0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return /^\s*(?:@\[[^\]\n]*\]\s*)*(?:private|local)\s+(?:def|theorem|inductive|structure|abbrev)\b/mu.test(stripped);
}

export function hasUnauditedLeanDeclarationForm0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return /^\s*(?:@\[[^\]\n]*\]\s*)*(?:class|instance|example|partial|macro|syntax|elab|scoped)\b/mu.test(stripped);
}
