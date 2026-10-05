// Concrete syntax for the playground: a parser and pretty-printers.
//
// This file is the UNVERIFIED shell. It turns text into the verified
// core's `Expr` and turns `Expr` / bytecode / values back into text.
// Nothing here affects what a program means — `evaluate` in core.ts does.
//
// Grammar (lowest precedence first):
//   expr := 'let' IDENT '=' expr 'in' expr
//         | 'if' expr 'then' expr 'else' expr
//         | cmp
//   cmp  := add (('<' | '==') add)?
//   add  := mul (('+' | '-') mul)*
//   mul  := atom (('*' | '/') atom)*
//   atom := NUMBER | 'true' | 'false' | IDENT | '(' expr ')'

import type { Expr, Op, Value, Fault, Instr, Result } from "./core.ts"

// ───────────────────────────── Tokens ─────────────────────────────

type Token =
  | { t: "num"; n: number; pos: number }
  | { t: "ident"; s: string; pos: number }
  | { t: "kw"; s: "let" | "in" | "if" | "then" | "else" | "true" | "false"; pos: number }
  | { t: "sym"; s: string; pos: number }
  | { t: "eof"; pos: number }

const KEYWORDS = new Set(["let", "in", "if", "then", "else", "true", "false"])

export class ParseError extends Error {
  readonly pos: number
  constructor(message: string, pos: number) {
    super(message)
    this.pos = pos
  }
}

function tokenize(src: string): Token[] {
  const out: Token[] = []
  let i = 0
  while (i < src.length) {
    const ch = src[i]
    if (/\s/.test(ch)) { i++; continue }
    if (/[0-9]/.test(ch)) {
      let j = i
      while (j < src.length && /[0-9]/.test(src[j])) j++
      out.push({ t: "num", n: Number(src.slice(i, j)), pos: i })
      i = j
      continue
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j++
      const s = src.slice(i, j)
      if (KEYWORDS.has(s)) out.push({ t: "kw", s: s as any, pos: i })
      else out.push({ t: "ident", s, pos: i })
      i = j
      continue
    }
    if (src.startsWith("==", i)) { out.push({ t: "sym", s: "==", pos: i }); i += 2; continue }
    if ("+-*/<=()".includes(ch)) { out.push({ t: "sym", s: ch, pos: i }); i++; continue }
    throw new ParseError(`Unexpected character '${ch}'`, i)
  }
  out.push({ t: "eof", pos: src.length })
  return out
}

// ───────────────────────────── Parser ─────────────────────────────

export function parse(src: string): Expr {
  const toks = tokenize(src)
  let k = 0
  const peek = () => toks[k]
  const next = () => toks[k++]
  const isSym = (s: string) => { const t = peek(); return t.t === "sym" && t.s === s }
  const isKw = (s: string) => { const t = peek(); return t.t === "kw" && t.s === s }
  const expectSym = (s: string) => {
    if (!isSym(s)) throw new ParseError(`Expected '${s}'`, peek().pos)
    next()
  }
  const expectKw = (s: string) => {
    if (!isKw(s)) throw new ParseError(`Expected '${s}'`, peek().pos)
    next()
  }

  function expr(): Expr {
    if (isKw("let")) {
      next()
      const t = next()
      if (t.t !== "ident") throw new ParseError("Expected a variable name after 'let'", t.pos)
      expectSym("=")
      const rhs = expr()
      expectKw("in")
      const body = expr()
      return { kind: "Let", x: t.s, rhs, body }
    }
    if (isKw("if")) {
      next()
      const cond = expr()
      expectKw("then")
      const thn = expr()
      expectKw("else")
      const els = expr()
      return { kind: "If", cond, thn, els }
    }
    return cmp()
  }

  function cmp(): Expr {
    const l = add()
    if (isSym("<")) { next(); return { kind: "Bin", op: "Lt", l, r: add() } }
    if (isSym("==")) { next(); return { kind: "Bin", op: "Eq", l, r: add() } }
    return l
  }

  function add(): Expr {
    let l = mul()
    for (;;) {
      if (isSym("+")) { next(); l = { kind: "Bin", op: "Add", l, r: mul() }; continue }
      if (isSym("-")) { next(); l = { kind: "Bin", op: "Sub", l, r: mul() }; continue }
      return l
    }
  }

  function mul(): Expr {
    let l = atom()
    for (;;) {
      if (isSym("*")) { next(); l = { kind: "Bin", op: "Mul", l, r: atom() }; continue }
      if (isSym("/")) { next(); l = { kind: "Bin", op: "Div", l, r: atom() }; continue }
      return l
    }
  }

  function atom(): Expr {
    const t = next()
    if (t.t === "num") return { kind: "Num", n: t.n }
    if (t.t === "kw" && t.s === "true") return { kind: "Bool", b: true }
    if (t.t === "kw" && t.s === "false") return { kind: "Bool", b: false }
    if (t.t === "ident") return { kind: "Var", x: t.s }
    if (t.t === "sym" && t.s === "(") {
      const e = expr()
      expectSym(")")
      return e
    }
    if (t.t === "eof") throw new ParseError("Unexpected end of input", t.pos)
    throw new ParseError(`Unexpected '${"s" in t ? t.s : "?"}'`, t.pos)
  }

  const e = expr()
  if (peek().t !== "eof") throw new ParseError("Unexpected trailing input", peek().pos)
  return e
}

// ───────────────────────── Pretty-printing ─────────────────────────

export const OP_SYMBOL: Record<Op, string> = {
  Add: "+", Sub: "-", Mul: "*", Div: "/", Lt: "<", Eq: "==",
}

const PREC: Record<Op, number> = { Lt: 1, Eq: 1, Add: 2, Sub: 2, Mul: 3, Div: 3 }

function prec(e: Expr): number {
  if (e.kind === "Bin") return PREC[e.op]
  if (e.kind === "Let" || e.kind === "If") return 0
  return 4
}

// Minimal parentheses; `let`/`if` bind loosest and extend to the right.
export function pretty(e: Expr): string {
  switch (e.kind) {
    case "Num": return String(e.n)
    case "Bool": return String(e.b)
    case "Var": return e.x
    case "Let": return `let ${e.x} = ${wrapLow(e.rhs)} in ${pretty(e.body)}`
    case "If": return `if ${wrapLow(e.cond)} then ${pretty(e.thn)} else ${pretty(e.els)}`
    case "Bin": {
      const p = PREC[e.op]
      const l = prec(e.l) < p ? `(${pretty(e.l)})` : pretty(e.l)
      const r = prec(e.r) <= p ? `(${pretty(e.r)})` : pretty(e.r)
      return `${l} ${OP_SYMBOL[e.op]} ${r}`
    }
  }
}

function wrapLow(e: Expr): string {
  return prec(e) === 0 ? `(${pretty(e)})` : pretty(e)
}

export function prettyValue(v: Value): string {
  return v.kind === "VNum" ? String(v.n) : String(v.b)
}

export const FAULT_TEXT: Record<Fault, string> = {
  DivByZero: "division by zero",
  Unbound: "unbound variable",
  TypeError: "type error",
  Underflow: "machine underflow",
}

export function prettyResult(r: Result): string {
  return r.kind === "Ok" ? prettyValue(r.v) : `⚠ ${FAULT_TEXT[r.why]}`
}

// One line per instruction, nested blocks indented — the shape of the
// structured bytecode the VM actually runs.
export type CodeLine = { depth: number; text: string; topIndex: number | null }

export function listing(code: Instr[], depth = 0, top = true): CodeLine[] {
  const out: CodeLine[] = []
  code.forEach((ins, i) => {
    const topIndex = top ? i : null
    switch (ins.kind) {
      case "Push": out.push({ depth, text: `push ${prettyValue(ins.v)}`, topIndex }); break
      case "Prim": out.push({ depth, text: `${ins.op.toLowerCase()}`, topIndex }); break
      case "Load": out.push({ depth, text: `load ${ins.x}`, topIndex }); break
      case "Bind": out.push({ depth, text: `bind ${ins.x}`, topIndex }); break
      case "Unbind": out.push({ depth, text: `unbind`, topIndex }); break
      case "Branch":
        out.push({ depth, text: `branch`, topIndex })
        out.push({ depth: depth + 1, text: `then:`, topIndex: null })
        out.push(...listing(ins.thn, depth + 2, false))
        out.push({ depth: depth + 1, text: `else:`, topIndex: null })
        out.push(...listing(ins.els, depth + 2, false))
        break
    }
  })
  return out
}

export function instrCount(code: Instr[]): number {
  let n = 0
  for (const ins of code) {
    n += 1
    if (ins.kind === "Branch") n += instrCount(ins.thn) + instrCount(ins.els)
  }
  return n
}
