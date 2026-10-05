# DESIGN — Optimist, a verified optimizing compiler

## 1. The product

Optimist is a compiler for a tiny expression language — integers, booleans, `let`, `if`, six
primitive operators — that type-checks a program, optimizes it, compiles it to a stack-machine
bytecode, and runs it. It ships as a single-page browser playground: you type a program, you
see every intermediate representation, you watch the machine execute step by step, and you see
the machine's answer next to a reference interpreter's. It is built for teaching: the audience
is anyone who has heard that compilers can be *proved* correct and wants to see what that means
at a scale that fits on a screen.

## 2. The promise — what is verified, and why

The verified core is `src/core.ts`. Every function in it is ordinary TypeScript; the `//@`
comments are its specification. The promises, in dependency order:

1. **The semantics is total.** `evaluate(e, env)` returns a `Result` for every program: a
   `Value`, or exactly one of four named `Fault`s. "What does this program mean" always has
   an answer, so every other promise can be stated as an equation against it.
2. **T1 — Type soundness.** If `typeOf(e, tenv)` is `Typed(t)`, then for every `env` with
   `envMatches(env, tenv)`: `evaluate(e, env)` is `Ok(v)` with `hasTy(v, t)`, or
   `Err(DivByZero)`. The faults `Unbound` and `TypeError` are impossible for accepted programs.
3. **T2 — Optimizer soundness.** For every `e`, `tenv`, `env` with `typeOf(e, tenv)` typed and
   `envMatches(env, tenv)`: `evaluate(optimize(e), env) === evaluate(e, env)`. Also
   `typeOf(optimize(e), tenv) === typeOf(e, tenv)` and `size(optimize(e)) <= size(e)`.
4. **T3 — Compiler correctness.** For every `e`, `env`, `stack` — *no typing hypothesis*:
   `evaluate(e, env)` is `Ok(v)` ⇒ `run(compile(e), stack, env) === halt([v, ...stack], env)`;
   `evaluate(e, env)` is `Err(f)` ⇒ `run(compile(e), stack, env) === crash(f)`.
5. **T4 — The pipeline.** `typeOf(e, []).kind === "Typed" ==> runPipeline(e) === evaluate(e, [])`.
6. **The foil is refuted.** `optimizeNaive`, the same rules without side conditions, is proved
   to violate the statement of T2 on a specific well-typed program (`NaiveMulZero`,
   `NaiveRefutesT2`), and the identity rule is proved to need the typing hypothesis
   (`IdentityNeedsTypes`).

**Trust boundary.** Not verified: the parser and pretty-printers (`src/syntax.ts`), the React
shell (`src/App.tsx`), and JavaScript's `number` being an IEEE double while the model is a
mathematical integer (exact below 2⁵³; the playground never leaves that range). The reference
semantics `evaluate` is the specification, not a proof target: the proofs establish that the
other stages agree with it, not that it is the semantics you wanted. No "verified end-to-end".

## 3. The key design insight

**Partiality is the whole story.** The language has one source of run-time failure that types
cannot see — division by zero — and that single fault is enough to make every classical
algebraic rewrite rule unsound as stated, because a rewrite that *deletes* a subexpression
also deletes the fault it might have raised, and a rewrite that *keeps* an operand can
change a type error into a value.

The architecture follows from taking that seriously:

- The semantics is a **total function into a sum type** (`Ok | Err`) rather than a partial
  function. Then "the optimizer preserves meaning" is a plain equation that also covers the
  failure cases, and "turning a crash into `0`" is a violation of it, not a grey area.
- The type checker is not an afterthought: **T1 is a lemma inside T2's proof.** The identity
  rules are sound because the surviving operand is an integer, and only the type system knows
  that. Stating T2 for well-typed programs is not a weakening; it is the precise hypothesis
  under which the rules are true.
- Deleting code needs a **totality witness**. `noDiv(e)` is syntactic, decidable, and together
  with T1 implies `evaluate(e, env).kind === "Ok"` (`NoDivTotal`). That lemma is the licence
  for `x * 0 → 0`.
- The bytecode has **structured control flow**. A `Branch` instruction carries its two blocks
  instead of jumping to an address. This makes `run` structurally recursive over the code, so
  the compiler-correctness proof is an induction over programs glued together by one
  concatenation lemma, with no program counter, no code-address arithmetic, and no
  "the jump target is still in range" invariants.
- **Environments are association lists**, in both the interpreter and the machine. `Let`
  evaluates its right-hand side and conses a binding; the machine's `Bind` pops a value and
  conses the same binding; `Unbind` pops it. Lexical scope is "the first match wins" in both
  worlds, so the two agree by construction and the proof never reasons about names.

## 4. Data model

```ts
//@ backend dafny
export type Op = "Add" | "Sub" | "Mul" | "Div" | "Lt" | "Eq";

export type Expr =
  | { kind: "Num"; n: number } | { kind: "Bool"; b: boolean } | { kind: "Var"; x: string }
  | { kind: "Let"; x: string; rhs: Expr; body: Expr }
  | { kind: "Bin"; op: Op; l: Expr; r: Expr }
  | { kind: "If"; cond: Expr; thn: Expr; els: Expr };

export type Value  = { kind: "VNum"; n: number } | { kind: "VBool"; b: boolean };
export type Fault  = "DivByZero" | "Unbound" | "TypeError" | "Underflow";
export type Result = { kind: "Ok"; v: Value } | { kind: "Err"; why: Fault };
export interface Binding { x: string; v: Value }     export type Env = Binding[];

export type Ty = "TInt" | "TBool";
export interface TBinding { x: string; t: Ty }       export type TEnv = TBinding[];
export type TyResult = { kind: "Typed"; t: Ty } | { kind: "IllTyped"; why: Fault };

export type Instr =
  | { kind: "Push"; v: Value } | { kind: "Prim"; op: Op } | { kind: "Load"; x: string }
  | { kind: "Bind"; x: string } | { kind: "Unbind" }
  | { kind: "Branch"; thn: Instr[]; els: Instr[] };
export type Stack = Value[];
export type Outcome = { kind: "Halt"; stack: Stack; env: Env } | { kind: "Crash"; why: Fault };
```

Representation choices, and why:

- **Variant names are capitalized** (`Num`, `Let`, `If`, `TInt`) because they become Dafny
  constructors, and `bool`, `if`, `let`, `var`, `int` are Dafny keywords or built-in types.
  Constructor names are also kept **unique across all datatypes** (`Ok`/`Err` vs
  `Typed`/`IllTyped` vs `Halt`/`Crash`) so no name is ambiguous in the generated Dafny.
- **`Fault` is shared** between the interpreter and the machine, so T3 can say "the machine
  crashes with *exactly* the interpreter's fault" as an equality on one type. `Underflow` is a
  machine-only fault (malformed bytecode); T3 implies compiled code never raises it.
- **Environments are lists, not maps.** `envMatches` is a positional zip; `lookup` and
  `lookupTy` are the same recursion; `Let`, `Bind`, and `Unbind` are cons and uncons. A map
  would force reasoning about key sets in every lemma.
- **`halt`/`crash`/`pushed` are tiny TypeScript functions**, not object literals, so they can
  appear verbatim in `//@ ensures` clauses (the spec grammar has no spread, and the constructor
  helpers give the spec the same vocabulary as the code).

The only invariant is the relation between the two environments, which is a function rather
than an `Inv(s)`:

- **M1** `envMatches(env, tenv)` ⇔ same length, same names in the same order, and
  `hasTy(env[i].v, tenv[i].t)` at every position.
- **M2** `envMatches([{x, v}, ...env], [{x, t}, ...tenv])` whenever `envMatches(env, tenv)` and
  `hasTy(v, t)` (`EnvMatchesExtend`). This is the only fact `Let` needs.

## 5. Architecture

```
┌──────────────────────────── unverified shell (browser) ─────────────────────────────┐
│  src/syntax.ts     parse: string → Expr          pretty: Expr → string, listing      │
│  src/App.tsx       chips · editor · 5 stage cards · verdict bar · theorem panel     │
│                    VM trace = run(code[0..k], [], []) for k = 0..n  (no 2nd machine) │
└───────────────────────────────┬─────────────────────────────────────────────────────┘
                                │ imports directly, no adapter
┌───────────────────────────────▼──────────── verified core: src/core.ts ─────────────┐
│                                                                                     │
│   Expr ──typeOf──▶ TyResult        T1: Typed(t) ⇒ evaluate is a t-value or DivByZero│
│    │                                                                                 │
│    ├──evaluate──▶ Result           the specification everything is measured against │
│    │                                                                                 │
│    ├──optimize──▶ Expr             T2: evaluate ∘ optimize = evaluate  (well-typed)  │
│    │     │   ↳ simplifyBin / simplifyIf   (folding, identities, guarded annihilation)│
│    │     ↳ optimizeNaive               the foil — refuted, not proven                │
│    │                                                                                 │
│    └──compile──▶ Instr[] ──run──▶ Outcome      T3: run ∘ compile = evaluate (all e)  │
│                                                                                     │
│   runPipeline = typeOf ▷ optimize ▷ compile ▷ run     T4: = evaluate  (well-typed)   │
└─────────────────────────────────────────────────────────────────────────────────────┘
                                │ lsc gen
                     src/core.dfy.gen  ──(additions only)──▶  src/core.dfy  ──▶ dafny verify
```

The shell does two things: turn text into an `Expr` and render what verified functions return.
There is no domain logic in `App.tsx` — the VM animation is produced by calling the verified
`run` on each prefix of the bytecode, so every state on screen is a value the proof speaks
about. The same `core.ts` could run on a server unchanged; nothing in it touches I/O.

## 6. Properties — the staged catalog

**Family A — Totality and well-formedness**

```ts
//@ ensures \result >= 1
function size(e: Expr): number
```
`evaluate`, `typeOf`, `run`, `compile` are total functions by construction (structural
`//@ decreases`); there is nothing to state beyond their types.

**Family B — Decision correctness: type soundness (T1)**

```ts
//@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Ok" ==> hasTy(evaluate(e, env).v, \result.t))
//@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Err" ==> evaluate(e, env).why === "DivByZero")
function typeOf(e: Expr, tenv: TEnv): TyResult
```
and its helper on variables:
```ts
//@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" ==> lookup(env, x).kind === "Ok" && hasTy(lookup(env, x).v, \result.t))
function lookupTy(tenv: TEnv, x: string): TyResult
```

**Family C — Conservation: optimizer preservation (T2)**

```ts
//@ ensures size(\result) <= size(e)
//@ ensures forall(tenv: TEnv, typeOf(e, tenv).kind === "Typed" ==> typeOf(\result, tenv) === typeOf(e, tenv))
//@ ensures forall(tenv: TEnv, forall(env: Env, typeOf(e, tenv).kind === "Typed" && envMatches(env, tenv) ==> evaluate(\result, env) === evaluate(e, env)))
function optimize(e: Expr): Expr
```
The same three clauses, specialized to one node, are the contracts of `simplifyBin` and
`simplifyIf` — which is what lets `optimize`'s proof be a plain induction.

**Family D — Refinement: compiler correctness (T3)**

```ts
//@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Ok" ==> run(\result, stack, env) === halt(pushed(evaluate(e, env).v, stack), env)))
//@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Err" ==> run(\result, stack, env) === crash(evaluate(e, env).why)))
function compile(e: Expr): Instr[]
```
Quantifying over the *initial* stack and environment is what makes the statement inductive:
the code for `l` runs on `stack`, the code for `r` runs on `[vl, ...stack]`.

**Family E — Composition (T4)**

```ts
//@ ensures typeOf(e, []).kind === "Typed" ==> \result === evaluate(e, [])
function runPipeline(e: Expr): Result
```

**Family F — Refutation (the foil)**, stated in `core.dfy` only, since it is about a
hypothetical rule:
```dafny
lemma NaiveRefutesT2()
  ensures exists e: Expr :: typeOf(e, []).Typed? && evaluate(optimizeNaive(e), []) != evaluate(e, [])
```

## 7. Verification approach

- **Pure recursive functions everywhere.** No loops, no `let`-mutation; every function in
  `core.ts` becomes a Dafny `function`, so the proofs are structural inductions and the
  functions can appear inside each other's specs.
- **Total kernel.** Nothing has a `requires`. Partiality is *data* (`Result`), which is why
  T2 and T3 can be equations.
- **Each `//@ ensures` is a separate generated lemma** (`optimize_ensures`, `compile_ensures`,
  …) with an empty body; the proof fills it in `core.dfy`. The pattern used throughout: an
  explicit-parameter lemma (`TypeSound(e, tenv, env)`, `OptimizeSem(e, tenv, env)`,
  `CompileCorrect(e, stack, env)`) proven by `match e` induction, and the generated lemma's
  body is a `forall` statement that instantiates it. Quantifiers never have to be
  instantiated by trigger luck.
- **One glue lemma for the machine.** `RunAppend(c1, c2, stack, env)`: running `c1 + c2` is
  running `c1`, then — if it halted — running `c2` from the resulting stack and environment.
  Induction on `c1`. Every `compile` case splits its output with it.
- **No escape hatches.** 0 `assume`, 0 `havoc`, 0 `extern`. The only arithmetic fact needed
  beyond Z3's linear reasoning is `JSFloorDiv(n, 1) == n` for the `x / 1 → x` rule, a
  one-line lemma.
- **Proof effort.** 56 verification conditions, 817 with `--isolate-assertions`, 0 errors,
  a few seconds of wall-clock. The proof file is ~2× the generated code.
- **Trust boundary (restated).** Parser, pretty-printer, React, and `number`-as-integer. The
  semantics `evaluate` is the specification.

## 8. Roadmap (staged proofs)

| Stage | Lands | Families | Status |
|---|---|---|---|
| 0 | `evaluate`, `typeOf` + T1, `lookupTy` soundness | A, B | done |
| 1 | `optimize` with folding, identities, guarded annihilation + T2; `NoDivTotal` | C | done |
| 2 | structured bytecode, `run`, `compile` + T3 via `RunAppend` | D | done |
| 3 | `runPipeline` + T4 | E | done |
| 4 | `optimizeNaive` and the three refutation lemmas; playground toggle | F | done |
| 5 | dead-`let` elimination (`let x = e in body` with `x ∉ FV(body)` → `body`, needs `noDiv(e)`) | C | open |
| 6 | `if c then t else t → t` (needs a structural `exprEq`; TS `===` is reference equality) | C | open |
| 7 | flat bytecode with relative jumps — the same T3, much harder proof | D | open (pedagogical contrast) |

Each stage was shippable; the playground is honest at every one.

## 9. Open questions / deferred

- **Idempotence** `optimize(optimize(e)) === optimize(e)`: likely true for this rule set
  (bottom-up, every rule shrinks), not yet stated.
- **Completeness of folding**: "every closed, division-free subterm becomes a literal" is a
  nice characterization of what the optimizer achieves, as opposed to what it preserves.
- **Parser–printer round trip** `parse(pretty(e)) === e` would move `syntax.ts` into the
  verified core; strings are in the fragment, so it is feasible, but it is a different lesson.
- **Numbers as `bigint`** would close the 2⁵³ caveat at the cost of `0n` literals throughout
  the teaching code; deliberately not done.
- **A `let`-aware optimizer** (constant propagation) needs substitution and capture
  reasoning — the natural next unit for a course that uses this as a base.
