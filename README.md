# Optimist

[![LemmaScript verified](https://img.shields.io/github/actions/workflow/status/midspiral/optimist-lemmascript/lemmascript.yml?branch=main&label=LemmaScript%20verified)](https://github.com/midspiral/optimist-lemmascript/actions/workflows/lemmascript.yml)

A **verified optimizing compiler** for a tiny language, written in ordinary TypeScript and
proven correct in Dafny with [LemmaScript](https://github.com/midspiral/LemmaScript). It runs
as a browser playground: type a program, watch it flow through *typecheck → optimize → compile →
run* on an animated stack machine, and see the machine's answer agree with the reference
interpreter's — not by luck, but because **every arrow between stages is a theorem**, and the
code on the page is the exact code those theorems are about.

This is a **LemmaScript case study** built for teaching. The whole compiler is one file,
[`src/core.ts`](src/core.ts) (~330 lines, half of them comments). Its specification is the
`//@` comments on its functions; its proofs are in [`src/core.dfy`](src/core.dfy).

## The idea in one screen

```
      source ──parse──▶ Expr ──typeOf──▶ Ty                      T1  type soundness
                         │
                         ├──evaluate──▶ Result   ◀── the reference semantics: what a program MEANS
                         │                 ║
                         └──optimize──▶ Expr      T2  same meaning, same type, no bigger
                                         │
                                        compile──▶ Instr[]        T3  the machine agrees with evaluate
                                                     │
                                                    run──▶ Outcome
                                                            ║
                   runPipeline(e) === evaluate(e, [])       T4  for every well-typed program
```

The language has integers, booleans, `let`, `if`, `+ - * /`, `<` and `==`. Integer division
floors and **dividing by zero is a run-time fault**, not infinity. That single design choice —
partiality — is what makes the optimizer interesting.

## The pedagogical twist

The rewrite rules everyone learns in school are *wrong* here:

| Rule | Looks obviously right | Counterexample | Why |
|---|---|---|---|
| `x + 0 → x` | `true + 0` is a **type error**; `true` is a value | `IdentityNeedsTypes` | the operand might not be an integer |
| `x * 0 → 0` | `(1 / 0) * 0` is a **crash**; `0` is a value | `NaiveMulZero` | the deleted operand might be hiding a fault |

The verifier rejects both as stated. What rescues them is the rest of the compiler:

- **Types rescue the identities.** T1 (type soundness) says a well-typed operand of `+` is an
  integer or a division-by-zero fault — never a boolean. So `x + 0 → x` is sound *for
  well-typed programs*, and T2 is stated for exactly those. The proof of the rewrite rule
  literally invokes the type soundness theorem.
- **Totality rescues the annihilations.** Deleting `x` in `x * 0` is only safe if `x` cannot
  fail. T1 leaves exactly one possible fault, division by zero, and a syntactic
  `noDiv(x)` check rules it out. So `x * 0 → 0` fires for `let x = 5 in x * 0` and is
  **refused** for `let y = 2 in (10 / y) * 0`.

Both unguarded rules survive in `optimizeNaive`, the foil. It has no theorem — it *cannot* have
one — and `core.dfy` proves concrete counterexamples against it (`NaiveMulZero`,
`NaiveRefutesT2`, `IdentityNeedsTypes`). The playground has a **verified / naive** toggle so
you can watch `(1 / 0) * 0` get miscompiled to `0` live.

Random testing, for the record, does not find this bug: the smoke test generates 5,000 random
programs and the naive optimizer gets every one of them right, because the bug needs a crash
*and* a multiply-by-literal-zero in the same term. Tests ask whether examples work. The proof
asks whether the bug is possible.

## What is verified

`lsc check` → **56 verification conditions, 0 errors** (817 under `--isolate-assertions`);
**0 `assume`s, 0 `havoc`s, 0 `extern`s**. Dafny 4.11.

- **T1 — Type soundness** (`typeOf`). If the checker accepts `e` at type `t`, then in every
  environment matching the typing environment, `evaluate(e, env)` is a value of type `t` or
  the fault `DivByZero`. Never `Unbound`, never `TypeError`. *"Well-typed programs don't go
  wrong — except for the one thing a type cannot see, the value of a divisor."*
- **T2 — Optimizer soundness** (`optimize`). For every well-typed program: the result is no
  larger (`size`), has the same type, and `evaluate(optimize(e), env) === evaluate(e, env)` in
  every matching environment — same value **or same fault**. A rewrite that turns a crash into
  an answer is a bug, and the spec says so.
- **T3 — Compiler correctness** (`compile`). For **every** program, typed or not, and every
  starting stack and environment: if `evaluate` says value `v`, `run(compile(e), stack, env)`
  halts with `v` pushed and the environment unchanged; if `evaluate` says fault `f`, the
  machine crashes with exactly `f`. The bytecode is a stack machine with **structured control
  flow** (a `Branch` carries its two blocks, like WebAssembly) and `Bind`/`Unbind` for scope.
- **T4 — The pipeline** (`runPipeline`). `typeOf(e, []).kind === "Typed" ==> runPipeline(e) ===
  evaluate(e, [])`. One line; it composes T2 and T3.
- **Totality lemma** (`NoDivTotal`, in `core.dfy`): well-typed + division-free ⇒ a value.
  This is the side condition the annihilation rule rests on.
- **Three counterexamples** (`NaiveMulZero`, `NaiveRefutesT2`, `IdentityNeedsTypes`): the exact
  statement T2 makes about `optimize` is *proved false* of `optimizeNaive`.

### What is *not* verified (the trust boundary, stated plainly)

The React playground, the parser and pretty-printer in `src/syntax.ts`, and the gap between
JavaScript `number` (a double) and the proof's mathematical integers (exact below 2⁵³). The
meaning of a program — `evaluate` — is the *specification*: everything else is proven against
it, but if you think `7 / 2` should be `3.5` rather than `3`, that is a disagreement with the
spec, not a bug the proof could catch. No "verified end-to-end" claim.

## Why it's a good case study

- **Compiler correctness is the canonical verification theorem** (CompCert, CakeML), and here
  the baby version is ~330 lines of TypeScript that a web page imports directly. The theorems
  are stated as `//@ ensures` on the functions themselves, in a form a programmer can read.
- **The proof structure *is* the lesson.** T2's proof calls T1. The annihilation rule's proof
  calls the totality lemma, which calls T1. You can see, in the dependency graph of the
  lemmas, *why* real compilers only optimize well-typed, well-defined programs.
- **It breaks legibly.** Drop the `noDiv(l)` guard in `simplifyBin` and Dafny says:
  ```
  Error: a postcondition could not be proved on this return path
    ensures evaluate(simplifyBin(op, l, r), env) == evaluate(Bin(op, l, r), env)
  ```
  Swap the two operand pops under `Prim` in `run` (so the top of the stack becomes the *left*
  operand) and T3 fails with `3 - 1` as the witness:
  ```
  Error: assertion might not hold
    assert run([Prim(op)], st, env) == run([], [res.v] + stack, env);
  ```
  Each takes seconds. Neither is something a test suite finds unless someone thought to try it.
- **Structured bytecode made the proof inductive.** Because `Branch` carries its blocks instead
  of jumping to an address, `run` is a structurally recursive function and the entire T3 proof
  is one `RunAppend` lemma ("running `c1 + c2` is running `c1`, then `c2` from where it left
  off") plus induction on the program. No program counters, no code-address arithmetic.

## Layout

```
src/core.ts        the verified core: syntax, evaluate, typeOf, optimize (+ naive foil),
                   bytecode, run, compile, runPipeline — with //@ specs
src/core.dfy.gen   generated Dafny — never edit
src/core.dfy       generated Dafny + hand-written proofs (additions only; CI diff-checks)
src/syntax.ts      UNVERIFIED: parser + pretty-printers for the playground
src/App.tsx        UNVERIFIED: the playground (React); every panel calls a verified function
test/smoke.ts      runtime witnesses: the examples, the counterexamples, 5,000 random programs
DESIGN.md          the design document (what is promised, why it's tractable, the proof plan)
LS_TUTORIAL.md     build-along tutorial, including what the prover rejected along the way
```

## Verify

```sh
npm install -g lemmascript     # the lsc CLI; Dafny 4.x on PATH
npm run verify                  # lsc check over LemmaScript-files.txt: regenerate, gate, verify
```

`lsc check` regenerates `src/core.dfy.gen` from the TypeScript, enforces that `src/core.dfy`
differs from it by **additions only**, and runs Dafny. If you change `src/core.ts`, run
`npm run regen` first — it three-way-merges the new generated code into `core.dfy`, keeping
the proofs. CI ([`.github/workflows/lemmascript.yml`](.github/workflows/lemmascript.yml)) does
the same and fails if a committed generated file is stale.

## Run

```sh
npm install
npm run dev          # the playground
npm test             # runtime smoke test of the verified core (node test/smoke.ts)
npm run typecheck
npm run build        # static site in dist/ (deployed to GitHub Pages by deploy.yml)
```

## A five-minute demo script

1. **Hello** — `let x = 6 * 7 in x + 0`. Point at the five stages. The optimizer folded
   `6 * 7` and deleted `+ 0`; the machine's stack animates to `42`; the verdict bar says the
   interpreter and the machine agree, *and cites T4 as the reason*.
2. **The trap** — `(1 / 0) * 0`. The type checker accepts it (it *is* well-typed). The
   interpreter says *division by zero*. The verified optimizer leaves it alone. Now flip the
   toggle to **naive**: the optimized program becomes `0`, the machine says `0`, the verdict bar
   turns red: *Miscompiled*.
3. **Why** — open `src/core.ts`, `simplifyBin`. Show the rule with its `noDiv(l)` guard and the
   `//@ ensures` above it. Delete `&& noDiv(l)`, run `npm run verify`, read the error aloud.
   Put the guard back; green. (Thirty seconds, and the audience has watched a prover refuse a
   plausible optimization.)
4. **Refused vs. Annihilate** — `let y = 2 in (10 / y) * 0` is left alone; `let x = 5 in x * 0`
   becomes `0`. Same rule, and the side condition is doing exactly what T1 licenses.
5. **The headline** — scroll to *The four theorems*, click *show the specs*. T4 is one line of
   `//@ ensures`. Everything on the page is a consequence of it.

## Status

Verified core + playground + tutorial. Possible extensions, each a theorem away: a `let`-
floating or dead-binding rule (needs a free-variable check), `if c then t else t → t` (needs a
structural-equality function, since TypeScript `===` on objects is reference equality — a
nice gotcha), a parser-printer round-trip proof, and a *flat* bytecode with jumps to show how
much harder T3 gets without structured control flow.

## License

MIT
