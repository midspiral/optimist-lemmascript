//@ backend dafny

// ═══════════════════════════════════════════════════════════════════════
// Optimist — a verified optimizing compiler for a tiny language
//
// One file, five stages, four theorems. Everything below is ordinary
// TypeScript: it is exactly what runs in the browser playground. The
// `//@` comments are the specification; LemmaScript translates this file
// to Dafny and the theorems are machine-checked there (see core.dfy).
//
//     source ──parse──▶ Expr ──typeOf──▶ Ty
//                        │
//                        ├──evaluate──▶ Result          (the reference semantics)
//                        │
//                        └──optimize──▶ Expr ──compile──▶ Instr[] ──run──▶ Outcome
//
//   T1  TYPE SOUNDNESS       a well-typed program never hits an unbound
//                            variable or a type error at run time; the only
//                            error it can still raise is division by zero.
//   T2  OPTIMIZER SOUNDNESS  for every well-typed program, the optimized
//                            program means exactly the same thing — the same
//                            value, or the same crash. Also: it has the same
//                            type, and it never gets bigger.
//   T3  COMPILER CORRECTNESS for every program (typed or not!), running the
//                            bytecode on the VM gives exactly what the
//                            interpreter gives — same value, or same crash.
//   T4  THE PIPELINE         typecheck → optimize → compile → run computes
//                            exactly evaluate(e, []) for every well-typed e.
//
// The pedagogical twist is in the optimizer. The rewrite rules everyone
// learns — x + 0 → x, x * 0 → 0 — are WRONG in a language with run-time
// type errors and division by zero: `true + 0` is an error but `true` is a
// value; `(1/0) * 0` is a crash but `0` is a value. The verifier rejects
// them. T1 is what rescues the identities (a well-typed `x` is an integer),
// and a syntactic totality check rescues the annihilations. The unguarded
// rules survive in `optimizeNaive`, with concrete counterexamples proved
// against them in core.dfy — and a toggle in the playground.
// ═══════════════════════════════════════════════════════════════════════

// ───────────────────────────── Syntax ─────────────────────────────

export type Op = "Add" | "Sub" | "Mul" | "Div" | "Lt" | "Eq";

export type Expr =
  | { kind: "Num"; n: number }
  | { kind: "Bool"; b: boolean }
  | { kind: "Var"; x: string }
  | { kind: "Let"; x: string; rhs: Expr; body: Expr }
  | { kind: "Bin"; op: Op; l: Expr; r: Expr }
  | { kind: "If"; cond: Expr; thn: Expr; els: Expr };

// Number of AST nodes. The optimizer promises never to increase it.
export function size(e: Expr): number {
  //@ decreases e
  //@ ensures \result >= 1
  if (e.kind === "Num") return 1;
  if (e.kind === "Bool") return 1;
  if (e.kind === "Var") return 1;
  if (e.kind === "Let") return 1 + size(e.rhs) + size(e.body);
  if (e.kind === "Bin") return 1 + size(e.l) + size(e.r);
  return 1 + size(e.cond) + size(e.thn) + size(e.els);
}

// ──────────────────────── Values and results ────────────────────────

export type Value =
  | { kind: "VNum"; n: number }
  | { kind: "VBool"; b: boolean };

// Everything that can go wrong at run time. `Underflow` is a machine
// fault (malformed bytecode); compiled code never raises it (T3).
export type Fault = "DivByZero" | "Unbound" | "TypeError" | "Underflow";

export type Result =
  | { kind: "Ok"; v: Value }
  | { kind: "Err"; why: Fault };

export interface Binding {
  x: string;
  v: Value;
}
export type Env = Binding[];

// Innermost binding wins (lexical shadowing).
export function lookup(env: Env, x: string): Result {
  //@ decreases env
  if (env.length === 0) return { kind: "Err", why: "Unbound" };
  if (env[0].x === x) return { kind: "Ok", v: env[0].v };
  return lookup(env.slice(1), x);
}

// Primitive operations. Integer division floors (like Python), and
// dividing by zero is an error, not infinity: this partiality is the
// whole reason the optimizer is interesting.
export function applyOp(op: Op, a: Value, b: Value): Result {
  if (a.kind === "VNum" && b.kind === "VNum") {
    if (op === "Add") return { kind: "Ok", v: { kind: "VNum", n: a.n + b.n } };
    if (op === "Sub") return { kind: "Ok", v: { kind: "VNum", n: a.n - b.n } };
    if (op === "Mul") return { kind: "Ok", v: { kind: "VNum", n: a.n * b.n } };
    if (op === "Div") {
      if (b.n === 0) return { kind: "Err", why: "DivByZero" };
      return { kind: "Ok", v: { kind: "VNum", n: Math.floor(a.n / b.n) } };
    }
    if (op === "Lt") return { kind: "Ok", v: { kind: "VBool", b: a.n < b.n } };
    return { kind: "Ok", v: { kind: "VBool", b: a.n === b.n } };
  }
  if (a.kind === "VBool" && b.kind === "VBool" && op === "Eq") {
    return { kind: "Ok", v: { kind: "VBool", b: a.b === b.b } };
  }
  return { kind: "Err", why: "TypeError" };
}

// ─────────────────────── The reference semantics ───────────────────────
//
// `evaluate` IS the meaning of a program. Every other stage is judged
// against it. It is total: every program either produces a value or a
// named fault, so "what the program means" is never undefined.

export function evaluate(e: Expr, env: Env): Result {
  //@ contract The meaning of a program: a value, or exactly one named fault. Total — it never fails to answer.
  //@ decreases e
  if (e.kind === "Num") return { kind: "Ok", v: { kind: "VNum", n: e.n } };
  if (e.kind === "Bool") return { kind: "Ok", v: { kind: "VBool", b: e.b } };
  if (e.kind === "Var") return lookup(env, e.x);
  if (e.kind === "Let") {
    const r1 = evaluate(e.rhs, env);
    if (r1.kind === "Err") return r1;
    return evaluate(e.body, [{ x: e.x, v: r1.v }, ...env]);
  }
  if (e.kind === "Bin") {
    const l = evaluate(e.l, env);
    if (l.kind === "Err") return l;
    const r = evaluate(e.r, env);
    if (r.kind === "Err") return r;
    return applyOp(e.op, l.v, r.v);
  }
  const c = evaluate(e.cond, env);
  if (c.kind === "Err") return c;
  if (c.v.kind !== "VBool") return { kind: "Err", why: "TypeError" };
  return c.v.b ? evaluate(e.thn, env) : evaluate(e.els, env);
}

// ───────────────────────────── Types ─────────────────────────────

export type Ty = "TInt" | "TBool";

export interface TBinding {
  x: string;
  t: Ty;
}
export type TEnv = TBinding[];

export type TyResult =
  | { kind: "Typed"; t: Ty }
  | { kind: "IllTyped"; why: Fault };

// A value inhabits a type.
export function hasTy(v: Value, t: Ty): boolean {
  if (v.kind === "VNum") return t === "TInt";
  return t === "TBool";
}

// A run-time environment is described by a typing environment:
// same names in the same order, every value inhabiting its type.
export function envMatches(env: Env, tenv: TEnv): boolean {
  //@ decreases env
  if (env.length === 0) return tenv.length === 0;
  if (tenv.length === 0) return false;
  return env[0].x === tenv[0].x && hasTy(env[0].v, tenv[0].t) && envMatches(env.slice(1), tenv.slice(1));
}

export function lookupTy(tenv: TEnv, x: string): TyResult {
  //@ decreases tenv
  // If the type checker finds x, the run-time lookup finds a value of that type.
  //@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" ==> lookup(env, x).kind === "Ok" && hasTy(lookup(env, x).v, \result.t))
  if (tenv.length === 0) return { kind: "IllTyped", why: "Unbound" };
  if (tenv[0].x === x) return { kind: "Typed", t: tenv[0].t };
  return lookupTy(tenv.slice(1), x);
}

export function opTy(op: Op, a: Ty, b: Ty): TyResult {
  if (a === "TInt" && b === "TInt") {
    if (op === "Lt" || op === "Eq") return { kind: "Typed", t: "TBool" };
    return { kind: "Typed", t: "TInt" };
  }
  if (a === "TBool" && b === "TBool" && op === "Eq") return { kind: "Typed", t: "TBool" };
  return { kind: "IllTyped", why: "TypeError" };
}

// T1 — TYPE SOUNDNESS. The two `ensures` say: if the checker accepts e
// at type t, then in any environment that matches tenv, evaluating e
// either yields a value of type t or fails with DivByZero. Never
// Unbound, never TypeError. "Well-typed programs don't go wrong" — except
// for the one thing a type cannot see, which is the value of a divisor.
export function typeOf(e: Expr, tenv: TEnv): TyResult {
  //@ contract Static type checking that is sound: an accepted program can only ever fail by dividing by zero, and if it succeeds its value has the predicted type.
  //@ decreases e
  //@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Ok" ==> hasTy(evaluate(e, env).v, \result.t))
  //@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Err" ==> evaluate(e, env).why === "DivByZero")
  if (e.kind === "Num") return { kind: "Typed", t: "TInt" };
  if (e.kind === "Bool") return { kind: "Typed", t: "TBool" };
  if (e.kind === "Var") return lookupTy(tenv, e.x);
  if (e.kind === "Let") {
    const t1 = typeOf(e.rhs, tenv);
    if (t1.kind === "IllTyped") return t1;
    return typeOf(e.body, [{ x: e.x, t: t1.t }, ...tenv]);
  }
  if (e.kind === "Bin") {
    const tl = typeOf(e.l, tenv);
    if (tl.kind === "IllTyped") return tl;
    const tr = typeOf(e.r, tenv);
    if (tr.kind === "IllTyped") return tr;
    return opTy(e.op, tl.t, tr.t);
  }
  const tc = typeOf(e.cond, tenv);
  if (tc.kind === "IllTyped") return tc;
  if (tc.t !== "TBool") return { kind: "IllTyped", why: "TypeError" };
  const tt = typeOf(e.thn, tenv);
  if (tt.kind === "IllTyped") return tt;
  const te = typeOf(e.els, tenv);
  if (te.kind === "IllTyped") return te;
  if (tt.t !== te.t) return { kind: "IllTyped", why: "TypeError" };
  return tt;
}

// ──────────────────────────── Optimizer ────────────────────────────
//
// A bottom-up rewriter. Each rule must preserve `evaluate` EXACTLY on
// well-typed programs: the same value, or the same fault. That rules
// out any rewrite that could turn a crash into an answer.

// Syntactic totality: no division anywhere inside. Together with T1,
// this is what makes it safe to DELETE a subexpression (x * 0 → 0):
// a well-typed, division-free expression cannot fail.
export function noDiv(e: Expr): boolean {
  //@ decreases e
  if (e.kind === "Num") return true;
  if (e.kind === "Bool") return true;
  if (e.kind === "Var") return true;
  if (e.kind === "Let") return noDiv(e.rhs) && noDiv(e.body);
  if (e.kind === "Bin") return e.op !== "Div" && noDiv(e.l) && noDiv(e.r);
  return noDiv(e.cond) && noDiv(e.thn) && noDiv(e.els);
}

export function valueToExpr(v: Value): Expr {
  if (v.kind === "VNum") return { kind: "Num", n: v.n };
  return { kind: "Bool", b: v.b };
}

// Rewrite one binary node whose children are already optimized.
export function simplifyBin(op: Op, l: Expr, r: Expr): Expr {
  //@ ensures size(\result) <= 1 + size(l) + size(r)
  //@ ensures forall(tenv: TEnv, typeOf({ kind: "Bin", op: op, l: l, r: r }, tenv).kind === "Typed" ==> typeOf(\result, tenv) === typeOf({ kind: "Bin", op: op, l: l, r: r }, tenv))
  //@ ensures forall(tenv: TEnv, forall(env: Env, typeOf({ kind: "Bin", op: op, l: l, r: r }, tenv).kind === "Typed" && envMatches(env, tenv) ==> evaluate(\result, env) === evaluate({ kind: "Bin", op: op, l: l, r: r }, env)))
  // Constant folding — but a division by zero is NOT folded away: it
  // stays in the program, because the program's meaning is "crash".
  if (l.kind === "Num" && r.kind === "Num") {
    const folded = applyOp(op, { kind: "VNum", n: l.n }, { kind: "VNum", n: r.n });
    if (folded.kind === "Ok") return valueToExpr(folded.v);
    return { kind: "Bin", op: op, l: l, r: r };
  }
  if (l.kind === "Bool" && r.kind === "Bool" && op === "Eq") {
    return { kind: "Bool", b: l.b === r.b };
  }
  // Identities. Sound only because T1 guarantees a well-typed operand
  // of `+` is an integer: `true + 0 → true` would change the meaning.
  if (op === "Add" && r.kind === "Num" && r.n === 0) return l;
  if (op === "Add" && l.kind === "Num" && l.n === 0) return r;
  if (op === "Sub" && r.kind === "Num" && r.n === 0) return l;
  if (op === "Mul" && r.kind === "Num" && r.n === 1) return l;
  if (op === "Mul" && l.kind === "Num" && l.n === 1) return r;
  if (op === "Div" && r.kind === "Num" && r.n === 1) return l;
  // Annihilation deletes the other operand, so it must be total too.
  if (op === "Mul" && r.kind === "Num" && r.n === 0 && noDiv(l)) return { kind: "Num", n: 0 };
  if (op === "Mul" && l.kind === "Num" && l.n === 0 && noDiv(r)) return { kind: "Num", n: 0 };
  return { kind: "Bin", op: op, l: l, r: r };
}

// Fold a conditional on a literal condition.
export function simplifyIf(c: Expr, t: Expr, e: Expr): Expr {
  //@ ensures size(\result) <= 1 + size(c) + size(t) + size(e)
  //@ ensures forall(tenv: TEnv, typeOf({ kind: "If", cond: c, thn: t, els: e }, tenv).kind === "Typed" ==> typeOf(\result, tenv) === typeOf({ kind: "If", cond: c, thn: t, els: e }, tenv))
  //@ ensures forall(tenv: TEnv, forall(env: Env, typeOf({ kind: "If", cond: c, thn: t, els: e }, tenv).kind === "Typed" && envMatches(env, tenv) ==> evaluate(\result, env) === evaluate({ kind: "If", cond: c, thn: t, els: e }, env)))
  if (c.kind === "Bool") return c.b ? t : e;
  return { kind: "If", cond: c, thn: t, els: e };
}

// T2 — OPTIMIZER SOUNDNESS. Three promises, for every well-typed program:
// it never grows, it keeps its type, and it means exactly the same thing
// in every matching environment — same value or same fault.
export function optimize(e: Expr): Expr {
  //@ contract Semantics-preserving optimization: for every well-typed program the result has the same type, is no larger, and evaluates to exactly the same value or the same fault in every matching environment.
  //@ decreases e
  //@ ensures size(\result) <= size(e)
  //@ ensures forall(tenv: TEnv, typeOf(e, tenv).kind === "Typed" ==> typeOf(\result, tenv) === typeOf(e, tenv))
  //@ ensures forall(tenv: TEnv, forall(env: Env, typeOf(e, tenv).kind === "Typed" && envMatches(env, tenv) ==> evaluate(\result, env) === evaluate(e, env)))
  if (e.kind === "Num") return e;
  if (e.kind === "Bool") return e;
  if (e.kind === "Var") return e;
  if (e.kind === "Let") return { kind: "Let", x: e.x, rhs: optimize(e.rhs), body: optimize(e.body) };
  if (e.kind === "Bin") return simplifyBin(e.op, optimize(e.l), optimize(e.r));
  return simplifyIf(optimize(e.cond), optimize(e.thn), optimize(e.els));
}

// ─────────────── The foil: the textbook rules, unguarded ───────────────
//
// This is what most people would write first. It has no theorem — it
// cannot have one. core.dfy proves two concrete counterexamples:
//   NaiveMulZero    (1 / 0) * 0   is well-typed and means DivByZero;
//                                  the naive optimizer says 0.
//   NaiveAddZero    true + 0       means TypeError; the naive optimizer
//                                  says true.

export function naiveBin(op: Op, l: Expr, r: Expr): Expr {
  if (l.kind === "Num" && r.kind === "Num") {
    const folded = applyOp(op, { kind: "VNum", n: l.n }, { kind: "VNum", n: r.n });
    if (folded.kind === "Ok") return valueToExpr(folded.v);
    return { kind: "Bin", op: op, l: l, r: r };
  }
  if (op === "Add" && r.kind === "Num" && r.n === 0) return l;
  if (op === "Add" && l.kind === "Num" && l.n === 0) return r;
  if (op === "Sub" && r.kind === "Num" && r.n === 0) return l;
  if (op === "Mul" && r.kind === "Num" && r.n === 1) return l;
  if (op === "Mul" && l.kind === "Num" && l.n === 1) return r;
  if (op === "Div" && r.kind === "Num" && r.n === 1) return l;
  if (op === "Mul" && r.kind === "Num" && r.n === 0) return { kind: "Num", n: 0 };
  if (op === "Mul" && l.kind === "Num" && l.n === 0) return { kind: "Num", n: 0 };
  return { kind: "Bin", op: op, l: l, r: r };
}

export function optimizeNaive(e: Expr): Expr {
  //@ decreases e
  //@ ensures size(\result) <= size(e)
  if (e.kind === "Num") return e;
  if (e.kind === "Bool") return e;
  if (e.kind === "Var") return e;
  if (e.kind === "Let") return { kind: "Let", x: e.x, rhs: optimizeNaive(e.rhs), body: optimizeNaive(e.body) };
  if (e.kind === "Bin") return naiveBin(e.op, optimizeNaive(e.l), optimizeNaive(e.r));
  return simplifyIf(optimizeNaive(e.cond), optimizeNaive(e.thn), optimizeNaive(e.els));
}

// ───────────────────── Bytecode and the machine ─────────────────────
//
// A stack machine with structured control flow, like WebAssembly: a
// `Branch` carries its two blocks instead of jumping to an address.
// `Bind`/`Unbind` push and pop the variable environment.

export type Instr =
  | { kind: "Push"; v: Value }
  | { kind: "Prim"; op: Op }
  | { kind: "Load"; x: string }
  | { kind: "Bind"; x: string }
  | { kind: "Unbind" }
  | { kind: "Branch"; thn: Instr[]; els: Instr[] };

export type Stack = Value[];

export type Outcome =
  | { kind: "Halt"; stack: Stack; env: Env }
  | { kind: "Crash"; why: Fault };

export function halt(stack: Stack, env: Env): Outcome {
  return { kind: "Halt", stack: stack, env: env };
}

export function crash(why: Fault): Outcome {
  return { kind: "Crash", why: why };
}

export function pushed(v: Value, stack: Stack): Stack {
  return [v, ...stack];
}

// Run a block of code to completion. Operands are popped right-then-left
// (the top of the stack is the RIGHT operand) — swap the two lines under
// `Prim` and T3 fails, with `3 - 1` as the witness.
export function run(code: Instr[], stack: Stack, env: Env): Outcome {
  //@ decreases code
  if (code.length === 0) return halt(stack, env);
  const ins = code[0];
  const rest = code.slice(1);
  if (ins.kind === "Push") return run(rest, [ins.v, ...stack], env);
  if (ins.kind === "Prim") {
    if (stack.length < 2) return crash("Underflow");
    const b = stack[0];
    const a = stack[1];
    const res = applyOp(ins.op, a, b);
    if (res.kind === "Err") return crash(res.why);
    return run(rest, [res.v, ...stack.slice(2)], env);
  }
  if (ins.kind === "Load") {
    const res = lookup(env, ins.x);
    if (res.kind === "Err") return crash(res.why);
    return run(rest, [res.v, ...stack], env);
  }
  if (ins.kind === "Bind") {
    if (stack.length < 1) return crash("Underflow");
    return run(rest, stack.slice(1), [{ x: ins.x, v: stack[0] }, ...env]);
  }
  if (ins.kind === "Unbind") {
    if (env.length < 1) return crash("Underflow");
    return run(rest, stack, env.slice(1));
  }
  if (stack.length < 1) return crash("Underflow");
  const c = stack[0];
  if (c.kind !== "VBool") return crash("TypeError");
  const inner = run(c.b ? ins.thn : ins.els, stack.slice(1), env);
  if (inner.kind === "Crash") return inner;
  return run(rest, inner.stack, inner.env);
}

// T3 — COMPILER CORRECTNESS. For EVERY program — well-typed or not — and
// every starting stack and environment: if the interpreter says the
// program is the value v, the machine halts with v pushed on the stack
// and the environment unchanged; if the interpreter says the program is
// fault f, the machine crashes with exactly f.
export function compile(e: Expr): Instr[] {
  //@ contract Compilation to the stack machine is correct: for every program and every initial stack and environment, running the code halts with exactly the interpreter's value pushed, or crashes with exactly the interpreter's fault.
  //@ decreases e
  //@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Ok" ==> run(\result, stack, env) === halt(pushed(evaluate(e, env).v, stack), env)))
  //@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Err" ==> run(\result, stack, env) === crash(evaluate(e, env).why)))
  if (e.kind === "Num") return [{ kind: "Push", v: { kind: "VNum", n: e.n } }];
  if (e.kind === "Bool") return [{ kind: "Push", v: { kind: "VBool", b: e.b } }];
  if (e.kind === "Var") return [{ kind: "Load", x: e.x }];
  if (e.kind === "Let") return [...compile(e.rhs), { kind: "Bind", x: e.x }, ...compile(e.body), { kind: "Unbind" }];
  if (e.kind === "Bin") return [...compile(e.l), ...compile(e.r), { kind: "Prim", op: e.op }];
  return [...compile(e.cond), { kind: "Branch", thn: compile(e.thn), els: compile(e.els) }];
}

// ──────────────────────────── The pipeline ────────────────────────────

// T4 — THE HEADLINE. Typecheck, optimize, compile, run. For every
// well-typed closed program, the answer that comes out of the machine
// is exactly the answer the reference interpreter gives.
export function runPipeline(e: Expr): Result {
  //@ contract The whole compiler pipeline — typecheck, optimize, compile, run — agrees with the reference interpreter on every well-typed program.
  //@ ensures typeOf(e, []).kind === "Typed" ==> \result === evaluate(e, [])
  const t = typeOf(e, []);
  if (t.kind === "IllTyped") return { kind: "Err", why: t.why };
  const out = run(compile(optimize(e)), [], []);
  if (out.kind === "Crash") return { kind: "Err", why: out.why };
  if (out.stack.length !== 1) return { kind: "Err", why: "Underflow" };
  return { kind: "Ok", v: out.stack[0] };
}
