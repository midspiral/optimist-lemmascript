# Building a verified compiler with LemmaScript — the tutorial

This is the build-along version of `src/core.ts`: the order things were written in, the
decisions, and — most usefully — the places where the prover said *no* and what that taught.
You can read it in fifteen minutes; reproducing it is an afternoon with an agent on a tight
`lsc check` loop.

Prerequisites: `npm i -g lemmascript`, Dafny 4.x on PATH. The loop is always the same:

```sh
lsc check src/core.ts      # regenerate core.dfy.gen, enforce additions-only, run Dafny
```

Edit the `.ts` → `lsc regen src/core.ts` (merges the new generated code into your proofs).
Edit only the `.dfy` → `lsc check`.

---

## 0. Decide what a program *means* first

A compiler is correct relative to a semantics. Before any optimizer or machine, write the
interpreter — and make it **total**:

```ts
export type Result = { kind: "Ok"; v: Value } | { kind: "Err"; why: Fault };

export function evaluate(e: Expr, env: Env): Result {
  //@ decreases e
  ...
}
```

Every program evaluates to a value or to one of four named faults. There is no `throw`, no
`undefined`, no "behavior is unspecified". This costs nothing at run time and it is what lets
every later theorem be an *equation*: `evaluate(optimize(e), env) === evaluate(e, env)` is a
meaningful sentence only if both sides always denote something.

Two LemmaScript habits start here:

- **Pure recursive functions, `const` only.** Loops and mutable `let` turn a function into a
  Dafny `method`, which cannot appear in a spec. Everything in `core.ts` is a `function`.
- **Capitalize your variant names.** `{ kind: "bool" }`, `{ kind: "if" }`, `{ kind: "let" }`
  would become Dafny constructors named `bool`, `if`, `let` — keywords. `Num / Bool / Var /
  Let / Bin / If` it is. Keep constructor names unique across *all* your unions, too
  (`Ok/Err`, `Typed/IllTyped`, `Halt/Crash`), so the generated Dafny is never ambiguous.

Run `lsc check`. With no `//@ ensures` yet there is nothing to prove, but you get to read
`core.dfy.gen` and confirm the `if`-chains on `e.kind` became a `match`.

## 1. The optimizer, first attempt — and the prover's first "no"

Write the textbook rules as a bottom-up rewriter and state what you believe about it:

```ts
export function optimize(e: Expr): Expr {
  //@ ensures forall(env: Env, evaluate(\result, env) === evaluate(e, env))
  ...
}
// with, in simplifyBin:
if (op === "Add" && r.kind === "Num" && r.n === 0) return l;      // x + 0 → x
if (op === "Mul" && r.kind === "Num" && r.n === 0) return { kind: "Num", n: 0 };  // x * 0 → 0
```

Dafny refuses. Both rules are false, and it is worth working out *why* by hand before reading
on:

- `true + 0` means **TypeError** (you cannot add a boolean). `true` means `true`. The rule
  `x + 0 → x` changed the program's meaning.
- `(1 / 0) * 0` means **DivByZero**. `0` means `0`. The rule `x * 0 → 0` deleted a crash.

In a language with run-time faults, a rewrite must preserve the faults too. There is no
"it would have crashed anyway" — the spec says *same value or same fault*, and the prover
holds you to it.

Both broken rules are kept in the finished file as `optimizeNaive`, and `core.dfy` proves the
two counterexamples (`NaiveMulZero`, `IdentityNeedsTypes`) as lemmas. The verifier did not
merely fail to prove the rules; the counterexamples are theorems.

## 2. Types rescue the identities (T1)

The identity rules are fine *if the operand is an integer*. Who knows that? A type checker.

```ts
export function typeOf(e: Expr, tenv: TEnv): TyResult {
  //@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Ok" ==> hasTy(evaluate(e, env).v, \result.t))
  //@ ensures forall(env: Env, envMatches(env, tenv) && \result.kind === "Typed" && evaluate(e, env).kind === "Err" ==> evaluate(e, env).why === "DivByZero")
```

That is type soundness, stated on the function that does the checking: an accepted program
evaluates to a value of the predicted type, or to **DivByZero** — never to `Unbound`, never to
`TypeError`. Division by zero is the one thing a type cannot see.

Note the shape: `envMatches(env, tenv)` is an ordinary boolean TypeScript function (same
names, same order, every value inhabiting its type), and `hasTy` likewise. Writing the
relations as code means the spec, the proof, and the playground all share one definition.

The proof in `core.dfy` is `TypeSound(e, tenv, env)` by `match e`. The `Let` case needs one
fact — that consing a well-typed binding onto matching environments keeps them matching
(`EnvMatchesExtend`) — and the `Bin` case needs that a primitive on well-typed operands never
raises `TypeError` (`ApplyOpTyped`, which Dafny proves by unfolding). Everything else is
"call the inductive hypothesis".

Now **restate T2 for well-typed programs**:

```ts
//@ ensures forall(tenv: TEnv, forall(env: Env, typeOf(e, tenv).kind === "Typed" && envMatches(env, tenv) ==> evaluate(\result, env) === evaluate(e, env)))
```

and the identity rules go through. In `SimplifyBinSem`, the proof of `x + 0 → x` is: by T1,
`evaluate(x, env)` is `Ok(VNum n)` or `Err(DivByZero)`; in the first case `n + 0 == n`, in the
second both sides are the same fault. The type soundness theorem is a *lemma in the optimizer's
proof*. That dependency is the single most important thing this case study has to teach.

## 3. Totality rescues the annihilations

`x * 0 → 0` is still refused, even for well-typed programs — `(1 / 0) * 0` is well-typed. The
rule *deletes* `x`, so it needs `x` to be unable to fail. T1 says the only possible fault is
division by zero, so a syntactic check suffices:

```ts
export function noDiv(e: Expr): boolean { ... }   // no Div anywhere inside

if (op === "Mul" && r.kind === "Num" && r.n === 0 && noDiv(l)) return { kind: "Num", n: 0 };
```

and the lemma that makes it sound:

```dafny
lemma NoDivTotal(e: Expr, tenv: TEnv, env: Env)
  requires envMatches(env, tenv) && typeOf(e, tenv).Typed? && noDiv(e)
  ensures evaluate(e, env).Ok?
```

Induction on `e`; the `Bin` case uses T1 again (well-typed operands, `op != Div` ⇒ `applyOp`
succeeds). Now `let x = 5 in x * 0` optimizes to `0` and `let y = 2 in (10 / y) * 0` is left
alone, and both behaviours are *required* by the theorem.

**Try it:** delete `&& noDiv(l)` and run `lsc check`. You get

```
core.dfy: Error: a postcondition could not be proved on this return path
  Related location: this is the postcondition that could not be proved
    ensures evaluate(simplifyBin(op, l, r), env) == evaluate(Bin(op, l, r), env)
```

in a few seconds. Put it back; green.

Two more clauses on `optimize` come almost for free and are worth having because they are
what a user of an optimizer actually wants to know:

```ts
//@ ensures size(\result) <= size(e)
//@ ensures forall(tenv: TEnv, typeOf(e, tenv).kind === "Typed" ==> typeOf(\result, tenv) === typeOf(e, tenv))
```

The second one — the optimizer preserves the type — is also what T4 will need, so that the
compiled program is still well-typed.

## 4. The machine, and why its bytecode is structured

A stack machine. The classic design has `Jmp`/`JmpIfFalse` with addresses; its correctness
proof needs a program counter, a "code at address `pc`" view, and lemmas about relocating
blocks. Instead, borrow WebAssembly's idea:

```ts
| { kind: "Branch"; thn: Instr[]; els: Instr[] }
```

A `Branch` *carries its two blocks*. `run` pops the condition, runs the chosen block to
completion, and continues with the rest. `run` is now structurally recursive on the code
(`//@ decreases code` — Dafny knows a block inside an instruction is smaller than the code
containing it), and the entire glue for the compiler proof is one lemma:

```dafny
lemma RunAppend(c1, c2, stack, env)
  ensures run(c1, stack, env).Crash? ==> run(c1 + c2, stack, env) == run(c1, stack, env)
  ensures run(c1, stack, env).Halt?  ==> run(c1 + c2, stack, env) == run(c2, run(c1,…).stack, run(c1,…).env)
```

Running `c1 + c2` is running `c1`, then `c2` from where it left off. Induction on `c1`, one
case per instruction.

Variables: the machine has `Load x`, `Bind x` (pop a value, cons a binding onto the
environment) and `Unbind` (uncons). `let x = rhs in body` compiles to
`compile(rhs) ++ [Bind x] ++ compile(body) ++ [Unbind]`, and because the interpreter *also*
uses a cons-list environment with first-match lookup, the two agree without any reasoning
about names.

## 5. Compiler correctness (T3)

```ts
//@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Ok" ==> run(\result, stack, env) === halt(pushed(evaluate(e, env).v, stack), env)))
//@ ensures forall(env: Env, forall(stack: Stack, evaluate(e, env).kind === "Err" ==> run(\result, stack, env) === crash(evaluate(e, env).why)))
```

Read it as: *whatever the interpreter says, the machine does — value pushed, environment
intact; or the identical crash.* Two things about the statement:

- It quantifies over the **initial stack**. That is not generality for its own sake: the code
  for the right operand runs on top of the left operand's value, so the inductive hypothesis
  must be usable at a different stack than the one you started with.
- It has **no typing hypothesis**. The compiler is correct for ill-typed programs too — it
  faithfully compiles `true + 0` to code that crashes with `TypeError`. T3 is about the
  translation, and the translation has nothing to do with types.

The proof, `CompileCorrect(e, stack, env)`, is `match e`: split `compile(e)` into its blocks
with `RunAppend`, apply the inductive hypothesis to each sub-program, and step the one
instruction that combines their results. The only hand-holding Dafny needed was
`assert st[0] == rv.v && st[1] == lv.v && st[2..] == stack` to see through
`[rv] + ([lv] + stack)`.

**Try it:** in `run`, swap `const b = stack[0]; const a = stack[1];` so the top of the stack
becomes the *left* operand. `lsc regen`, then:

```
core.dfy: Error: assertion might not hold
    assert run([Prim(op)], st, env) == run([], [res.v] + stack, env);
```

`3 - 1` now compiles to code that computes `-2`. A test suite catches this if someone wrote a
subtraction test with distinct operands; the prover catches it unconditionally.

Small LemmaScript note: the spec grammar has no spread, so `[v, ...stack]` cannot appear in an
`ensures`. `pushed(v, stack)`, `halt(stack, env)` and `crash(why)` are three-line TypeScript
functions that exist so the spec can say exactly what the code says.

## 6. The headline (T4)

```ts
export function runPipeline(e: Expr): Result {
  //@ ensures typeOf(e, []).kind === "Typed" ==> \result === evaluate(e, [])
```

Typecheck, optimize, compile, run; for every well-typed closed program the answer is the
interpreter's. The proof is four lines: T2 at the empty environments (`envMatches([], [])` is
`true`) gives `evaluate(optimize(e), [])`; T3 on `optimize(e)` gives the machine's outcome;
Dafny matches the `Halt([v], [])` against `runPipeline`'s `|stack| == 1` check.

## 7. The foil, kept on purpose

`optimizeNaive` is the step-1 optimizer, unchanged, left in the file. It has one weak contract
(`size` does not grow) and three lemmas *against* it in `core.dfy`:

```dafny
lemma NaiveRefutesT2()
  ensures exists e: Expr :: typeOf(e, []).Typed? && evaluate(optimizeNaive(e), []) != evaluate(e, [])
```

That is the literal negation of T2's conclusion, proved with `(1 / 0) * 0` as the witness. The
playground's **verified / naive** toggle runs it. A verified codebase can contain code that is
known-wrong — as long as the file says so in a theorem and nothing with a correctness contract
calls it.

## 8. What the loop looked like

- `lsc check` first run: 21 lemmas discharged automatically (sizes, `simplifyIf`, …), 11
  generated `_ensures` lemmas failing with empty bodies — the expected state.
- One pass writing the helper lemmas above as **additions at the end of `core.dfy`** and
  one-line `forall … { Helper(e, …); }` bodies inside each generated lemma: 56 verified,
  0 errors. Nothing needed a second attempt; the design choices in §0 and §4 are why.
- `dafny verify --isolate-assertions`: 817 assertions, 0 errors, seconds.
- `node test/smoke.ts`: the examples, the counterexamples, and 5,000 random programs run
  through the real TypeScript. The random search did not find the naive optimizer's bug —
  which is the point.

## 9. Where to take it

Each of these is one theorem away and would make a good exercise:

1. **Dead `let`**: `let x = e in body → body` when `x ∉ FV(body)` and `noDiv(e)`. Needs a
   free-variable function and a lemma that evaluation ignores unused bindings.
2. **`if c then t else t → t`**: needs `exprEq(t, t')` written out, because TypeScript `===` on
   objects is reference equality while the generated Dafny `==` is structural — a real
   semantic gap that LemmaScript would otherwise paper over.
3. **Idempotence**: `optimize(optimize(e)) === optimize(e)`.
4. **Flat bytecode**: replace `Branch` with relative jumps and re-prove T3. Measuring how much
   longer the proof gets is the lesson about structured control flow.
