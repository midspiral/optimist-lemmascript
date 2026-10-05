// Runtime witnesses for the verified properties.
//
// The theorems in src/core.ts are proven for ALL programs; this file
// just runs the actual TypeScript on a few hundred of them to make
// sure the thing that was verified is the thing that ships.
//   node test/smoke.ts

import {
  evaluate, typeOf, optimize, optimizeNaive, compile, run, runPipeline, size, noDiv,
  type Expr, type Result,
} from "../src/core.ts"
import { parse, pretty, prettyResult } from "../src/syntax.ts"

let failures = 0
function check(cond: boolean, msg: string) {
  if (!cond) { failures++; console.error("  FAIL", msg) }
}
function same(a: Result, b: Result): boolean {
  return JSON.stringify(a) === JSON.stringify(b)
}

// ── Named examples (the ones in the playground) ──
const EXAMPLES: Array<[string, string]> = [
  ["let x = 6 * 7 in x + 0", "42"],
  ["(2 + 3) * (10 - 4)", "30"],
  ["if 2 < 3 then 10 else 1 / 0", "10"],
  ["let x = 1 in let x = x + 1 in x * 10", "20"],
  ["let x = 5 in x * 0", "0"],
  ["let y = 2 in (10 / y) * 0", "0"],
  ["(1 / 0) * 0", "⚠ division by zero"],
  ["7 / 2", "3"],
  ["0 - 7 / 2", "-3"],
  ["(0 - 7) / 2", "-4"],
  ["true == (1 < 2)", "true"],
]
console.log("examples")
for (const [src, expected] of EXAMPLES) {
  const e = parse(src)
  const r = runPipeline(e)
  check(prettyResult(r) === expected, `${src} → ${prettyResult(r)}, expected ${expected}`)
  check(same(r, evaluate(e, [])), `T4 on ${src}`)
  check(parse(pretty(e)).toString() === e.toString() && same(evaluate(parse(pretty(e)), []), evaluate(e, [])),
    `pretty/parse round trip on ${src}`)
}

// ── Type checker rejects what it should ──
console.log("type checker")
check(typeOf(parse("if 1 then 2 else 3"), []).kind === "IllTyped", "if on an int is rejected")
check(typeOf(parse("x + 1"), []).kind === "IllTyped", "unbound variable is rejected")
check(typeOf(parse("true + 0"), []).kind === "IllTyped", "true + 0 is rejected")
check(typeOf(parse("if true then 1 else false"), []).kind === "IllTyped", "mismatched branches are rejected")
check(runPipeline(parse("x + 1")).kind === "Err" && (runPipeline(parse("x + 1")) as any).why === "Unbound",
  "pipeline reports the type checker's fault")

// ── The counterexamples proved in core.dfy, witnessed at run time ──
console.log("counterexamples")
{
  const e = parse("(1 / 0) * 0")
  check(typeOf(e, []).kind === "Typed", "NaiveMulZero: well-typed")
  check(prettyResult(evaluate(e, [])) === "⚠ division by zero", "NaiveMulZero: means crash")
  check(prettyResult(evaluate(optimizeNaive(e), [])) === "0", "NaiveMulZero: naive says 0")
  check(pretty(optimize(e)) === pretty(e), "NaiveMulZero: verified optimizer leaves it alone")
}
{
  const e = parse("true + 0")
  check(typeOf(e, []).kind === "IllTyped", "IdentityNeedsTypes: ill-typed")
  check(prettyResult(evaluate(e, [])) === "⚠ type error", "IdentityNeedsTypes: means type error")
  check(prettyResult(evaluate(optimizeNaive(e), [])) === "true", "IdentityNeedsTypes: naive says true")
}

// ── Random programs: T2, T3, T4 on a few hundred generated terms ──
console.log("random programs")
let seed = 20261004
function rnd(n: number): number {
  // mulberry32
  seed = (seed + 0x6d2b79f5) | 0
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
  return ((t ^ (t >>> 14)) >>> 0) % n
}
const OPS = ["Add", "Sub", "Mul", "Div", "Lt", "Eq"] as const
function gen(depth: number, vars: string[]): Expr {
  const r = rnd(depth <= 0 ? 3 : 10)
  if (r === 0) return { kind: "Num", n: rnd(5) - 1 }
  if (r === 1) return { kind: "Bool", b: rnd(2) === 0 }
  if (r === 2) return vars.length ? { kind: "Var", x: vars[rnd(vars.length)] } : { kind: "Num", n: rnd(3) }
  if (r <= 6) return { kind: "Bin", op: OPS[rnd(OPS.length)], l: gen(depth - 1, vars), r: gen(depth - 1, vars) }
  if (r <= 8) {
    const x = "xyz"[rnd(3)]
    return { kind: "Let", x, rhs: gen(depth - 1, vars), body: gen(depth - 1, [x, ...vars]) }
  }
  return { kind: "If", cond: gen(depth - 1, vars), thn: gen(depth - 1, vars), els: gen(depth - 1, vars) }
}
let typed = 0, crashes = 0, shrunk = 0, naiveDisagreements = 0
for (let i = 0; i < 5000; i++) {
  const e = gen(4, [])
  const ref = evaluate(e, [])
  // T3 holds for EVERY program, typed or not.
  const out = run(compile(e), [], [])
  if (ref.kind === "Ok") check(out.kind === "Halt" && out.stack.length === 1 && same({ kind: "Ok", v: out.stack[0] }, ref), `T3 value on ${pretty(e)}`)
  else check(out.kind === "Crash" && out.why === ref.why, `T3 fault on ${pretty(e)}`)
  if (typeOf(e, []).kind !== "Typed") continue
  typed++
  if (ref.kind === "Err") { crashes++; check(ref.why === "DivByZero", `T1: only DivByZero on ${pretty(e)}`) }
  const o = optimize(e)
  check(same(evaluate(o, []), ref), `T2 semantics on ${pretty(e)}`)
  check(size(o) <= size(e), `T2 size on ${pretty(e)}`)
  if (size(o) < size(e)) shrunk++
  check(JSON.stringify(typeOf(o, [])) === JSON.stringify(typeOf(e, [])), `T2 type on ${pretty(e)}`)
  check(same(runPipeline(e), ref), `T4 on ${pretty(e)}`)
  if (!same(evaluate(optimizeNaive(e), []), ref)) naiveDisagreements++
  if (noDiv(e)) check(ref.kind === "Ok", `NoDivTotal on ${pretty(e)}`)
}
console.log(`  ${typed} well-typed programs, ${crashes} of which divide by zero; optimizer shrank ${shrunk}`)
// Random testing usually does NOT find the naive optimizer's bug: it needs a
// crashing subterm multiplied by a literal zero in the same program. That is
// the point — the witness lemmas in core.dfy pin the bug down exactly.
console.log(`  naive optimizer changed the meaning of ${naiveDisagreements} random program(s)` +
  (naiveDisagreements === 0 ? " — random testing missed the bug that NaiveMulZero proves" : ""))

if (failures) throw new Error(`${failures} failure(s)`)
console.log("all good")
