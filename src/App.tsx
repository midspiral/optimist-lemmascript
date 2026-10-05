// The playground: an UNVERIFIED shell around the verified core.
//
// Everything that has a meaning is computed by core.ts: parsing produces an
// `Expr`, and from there every panel shows the output of a verified function
// (typeOf, optimize, compile, run, evaluate). The VM trace is built by running
// the verified `run` on successive prefixes of the bytecode — there is no
// second, "display" implementation of the machine.

import { useEffect, useMemo, useState } from "react"
import {
  evaluate, typeOf, optimize, optimizeNaive, compile, run, size,
  type Expr, type Instr, type Outcome, type Result, type TyResult, type Value, type Binding,
} from "./core.ts"
import {
  parse, ParseError, pretty, prettyValue, prettyResult, FAULT_TEXT, OP_SYMBOL, listing, instrCount,
} from "./syntax.ts"
import coreSource from "./core.ts?raw"

// ───────────────────────────── Examples ─────────────────────────────

const EXAMPLES: { name: string; src: string; blurb: string }[] = [
  { name: "Hello", src: "let x = 6 * 7 in x + 0",
    blurb: "Constant folding (6 * 7 → 42) and an identity (x + 0 → x). The identity is only sound because the type checker guarantees x is an integer." },
  { name: "Dead branch", src: "if 2 < 3 then 10 else 1 / 0",
    blurb: "The condition folds to true, so the whole conditional folds to 10. The crash in the dead branch is deleted — soundly, because it was never going to be evaluated." },
  { name: "Shadowing", src: "let x = 1 in let x = x + 1 in x * 10",
    blurb: "Lexical scope: the inner x shadows the outer one. On the machine, bind/unbind push and pop the environment." },
  { name: "Annihilate", src: "let x = 5 in x * 0",
    blurb: "x * 0 → 0 fires: x is well-typed and division-free, so by T1 it cannot fail, so deleting it loses nothing." },
  { name: "Refused", src: "let y = 2 in (10 / y) * 0",
    blurb: "(10 / y) * 0 is NOT rewritten. The optimizer cannot prove 10 / y is safe (y could be 0 in some environment), and a rewrite that could turn a crash into a 0 would break T2." },
  { name: "The trap", src: "(1 / 0) * 0",
    blurb: "Well-typed — the type checker accepts it — and its meaning is a crash. The verified optimizer leaves it alone. Switch to the naive optimizer and watch it become 0." },
  { name: "Ill-typed", src: "if 1 then 2 else 3",
    blurb: "The type checker rejects it, so the pipeline stops. T2 says nothing about ill-typed programs — and it couldn't: see IdentityNeedsTypes in core.dfy." },
  { name: "Floor", src: "(0 - 7) / 2",
    blurb: "Integer division floors, so −7 / 2 is −4 — in the interpreter, in the machine, and in the proof (JSFloorDiv is the exact lowering of Math.floor(a / b))." },
]

// ─────────────────────── Spec extraction (for display) ───────────────────────

// Pull the `//@` lines that sit at the top of a function body in core.ts, so
// the page shows the real specification, not a paraphrase of it.
function specOf(fn: string): string[] {
  const lines = coreSource.split("\n")
  const start = lines.findIndex((l) => l.startsWith(`export function ${fn}(`))
  if (start < 0) return []
  const out: string[] = []
  for (let i = start + 1; i < lines.length; i++) {
    const t = lines[i].trim()
    if (t.startsWith("//@")) out.push(t.replace(/^\/\/@\s*/, ""))
    else if (t.startsWith("//")) continue
    else break
  }
  return out.filter((l) => !l.startsWith("decreases") && !l.startsWith("contract"))
}

// ───────────────────────────── Analysis ─────────────────────────────

type Analysis =
  | { ok: false; error: ParseError }
  | {
      ok: true
      ast: Expr
      ty: TyResult
      ref: Result            // the reference semantics: evaluate(ast, [])
      opt: Expr | null       // null when the type checker rejected the program
      code: Instr[] | null
      trace: Outcome[] | null  // trace[k] = run(code[0..k], [], [])
      machine: Result | null
    }

function outcomeToResult(o: Outcome): Result {
  if (o.kind === "Crash") return { kind: "Err", why: o.why }
  if (o.stack.length !== 1) return { kind: "Err", why: "Underflow" }
  return { kind: "Ok", v: o.stack[0] }
}

function analyze(src: string, naive: boolean): Analysis {
  let ast: Expr
  try {
    ast = parse(src)
  } catch (e) {
    if (e instanceof ParseError) return { ok: false, error: e }
    throw e
  }
  const ty = typeOf(ast, [])
  const ref = evaluate(ast, [])
  if (ty.kind === "IllTyped") return { ok: true, ast, ty, ref, opt: null, code: null, trace: null, machine: null }
  const opt = naive ? optimizeNaive(ast) : optimize(ast)
  const code = compile(opt)
  const trace: Outcome[] = []
  for (let k = 0; k <= code.length; k++) trace.push(run(code.slice(0, k), [], []))
  const machine = outcomeToResult(trace[trace.length - 1])
  return { ok: true, ast, ty, ref, opt, code, trace, machine }
}

function sameResult(a: Result, b: Result): boolean {
  return JSON.stringify(a) === JSON.stringify(b)
}

// ───────────────────────────── Components ─────────────────────────────

function AstTree({ e }: { e: Expr }) {
  switch (e.kind) {
    case "Num": return <div className="ast-leaf"><span className="ast-kind">Num</span> {e.n}</div>
    case "Bool": return <div className="ast-leaf"><span className="ast-kind">Bool</span> {String(e.b)}</div>
    case "Var": return <div className="ast-leaf"><span className="ast-kind">Var</span> {e.x}</div>
    case "Let":
      return (
        <div className="ast-node">
          <div><span className="ast-kind">Let</span> {e.x}</div>
          <div className="ast-children"><AstTree e={e.rhs} /><AstTree e={e.body} /></div>
        </div>
      )
    case "Bin":
      return (
        <div className="ast-node">
          <div><span className="ast-kind">Bin</span> {OP_SYMBOL[e.op]}</div>
          <div className="ast-children"><AstTree e={e.l} /><AstTree e={e.r} /></div>
        </div>
      )
    case "If":
      return (
        <div className="ast-node">
          <div><span className="ast-kind">If</span></div>
          <div className="ast-children"><AstTree e={e.cond} /><AstTree e={e.thn} /><AstTree e={e.els} /></div>
        </div>
      )
  }
}

function ValueChip({ v }: { v: Value }) {
  return <span className={"val " + (v.kind === "VNum" ? "val-num" : "val-bool")}>{prettyValue(v)}</span>
}

function MachineState({ o }: { o: Outcome }) {
  if (o.kind === "Crash") {
    return <div className="machine-crash">crash: {FAULT_TEXT[o.why]}</div>
  }
  return (
    <div className="machine-state">
      <div className="machine-col">
        <div className="machine-label">stack</div>
        <div className="stack">
          {o.stack.length === 0 && <div className="stack-empty">empty</div>}
          {o.stack.map((v, i) => (
            <div key={i} className={"stack-cell " + (i === 0 ? "stack-top" : "")}><ValueChip v={v} /></div>
          ))}
        </div>
      </div>
      <div className="machine-col">
        <div className="machine-label">env</div>
        <div className="env">
          {o.env.length === 0 && <div className="stack-empty">empty</div>}
          {o.env.map((b: Binding, i: number) => (
            <div key={i} className="env-cell">{b.x} = <ValueChip v={b.v} /></div>
          ))}
        </div>
      </div>
    </div>
  )
}

function Listing({ code, active }: { code: Instr[]; active: number | null }) {
  const lines = listing(code)
  return (
    <pre className="listing">
      {lines.map((ln, i) => (
        <div key={i} className={"listing-line " + (ln.topIndex !== null && ln.topIndex === active ? "active" : "")}
             style={{ paddingLeft: 8 + ln.depth * 14 }}>
          {ln.topIndex !== null && <span className="listing-idx">{ln.topIndex + 1}</span>}
          {ln.text}
        </div>
      ))}
    </pre>
  )
}

function Spec({ fn }: { fn: string }) {
  const lines = specOf(fn)
  return (
    <pre className="spec">
      {lines.map((l, i) => <div key={i}>{"//@ " + l}</div>)}
    </pre>
  )
}

function Stage({ n, title, theorem, children, muted, badge }: {
  n: number; title: string; theorem?: string; children: React.ReactNode; muted?: boolean; badge?: React.ReactNode
}) {
  return (
    <section className={"stage " + (muted ? "stage-muted" : "")}>
      <header className="stage-head">
        <span className="stage-num">{n}</span>
        <h3>{title}</h3>
        {badge}
        {theorem && <span className="theorem-tag">{theorem}</span>}
      </header>
      <div className="stage-body">{children}</div>
    </section>
  )
}

// ───────────────────────────── App ─────────────────────────────

export default function App() {
  const [src, setSrc] = useState(EXAMPLES[0].src)
  const [naive, setNaive] = useState(false)
  const [step, setStep] = useState(0)
  const [playing, setPlaying] = useState(true)
  const [showProofs, setShowProofs] = useState(false)

  const a = useMemo(() => analyze(src, naive), [src, naive])
  const example = EXAMPLES.find((x) => x.src === src)

  const nSteps = a.ok && a.code ? a.code.length : 0

  // Restart the animation whenever the program or the optimizer changes.
  // Done as derived state during render (not in an effect) so the ticking
  // effect below never sees a stale `step` from the previous program.
  const runKey = src + "\u0000" + naive
  const [prevRunKey, setPrevRunKey] = useState(runKey)
  if (runKey !== prevRunKey) {
    setPrevRunKey(runKey)
    setStep(0)
    setPlaying(true)
  }
  useEffect(() => {
    if (!playing) return
    if (step >= nSteps) { setPlaying(false); return }
    const t = window.setTimeout(() => setStep((s) => s + 1), 420)
    return () => window.clearTimeout(t)
  }, [playing, step, nSteps])

  const agree = a.ok && a.machine ? sameResult(a.ref, a.machine) : null

  return (
    <div className="page">
      <header className="masthead">
        <div>
          <h1><span className="logo" aria-hidden>▲</span> Optimist</h1>
          <p className="tagline">
            A verified optimizing compiler for a tiny language. Written in TypeScript, specified in <code>//@</code> comments,
            proven in Dafny by <a href="https://github.com/midspiral/LemmaScript">LemmaScript</a>.
            The code running on this page <em>is</em> the code that was proven.
          </p>
        </div>
        <div className="proof-badge" title="dafny verify src/core.dfy">
          <div className="proof-badge-big">0 errors</div>
          <div>56 verification conditions · 817 with --isolate-assertions</div>
          <div>4 theorems · 3 counterexamples · 0 assumes</div>
        </div>
      </header>

      <section className="editor">
        <div className="chips">
          {EXAMPLES.map((ex) => (
            <button key={ex.name} className={"chip " + (ex.src === src ? "chip-on" : "")} onClick={() => setSrc(ex.src)}>
              {ex.name}
            </button>
          ))}
        </div>
        <textarea
          className="source"
          value={src}
          spellCheck={false}
          rows={2}
          onChange={(e) => setSrc(e.target.value)}
          aria-label="Program source"
        />
        {!a.ok && <div className="parse-error">Parse error at position {a.error.pos}: {a.error.message}</div>}
        {example && <p className="blurb">{example.blurb}</p>}
        <p className="grammar">
          <code>let x = e in e</code> · <code>if e then e else e</code> · <code>+ − * /</code> · <code>&lt; ==</code> · integers · <code>true</code> <code>false</code>
        </p>
      </section>

      {a.ok && (
        <>
          <div className="pipeline">
            <Stage n={1} title="Parse">
              <div className="pretty">{pretty(a.ast)}</div>
              <div className="ast"><AstTree e={a.ast} /></div>
              <div className="meta">{size(a.ast)} nodes</div>
            </Stage>

            <Stage n={2} title="Typecheck" theorem="T1 soundness">
              {a.ty.kind === "Typed"
                ? <div className="ty-ok">: {a.ty.t === "TInt" ? "Int" : "Bool"}</div>
                : <div className="ty-bad">rejected: {FAULT_TEXT[a.ty.why]}</div>}
              <p className="note">
                {a.ty.kind === "Typed"
                  ? <>By T1, running this program can yield a value of this type or <em>division by zero</em> — nothing else. No unbound variable, no type error, ever.</>
                  : <>The pipeline stops here. The theorems about the optimizer (T2) and the pipeline (T4) are stated for well-typed programs — and they have to be: <code>true + 0 → true</code> would change this program's meaning.</>}
              </p>
            </Stage>

            <Stage n={3} title="Optimize" theorem={naive ? undefined : "T2 preservation"} muted={!a.opt}
                   badge={
                     <span className="toggle" role="group" aria-label="Optimizer">
                       <button className={!naive ? "on" : ""} onClick={() => setNaive(false)}>verified</button>
                       <button className={naive ? "on naive-on" : ""} onClick={() => setNaive(true)}>naive</button>
                     </span>
                   }>
              {a.opt ? (
                <>
                  <div className={"pretty " + (naive ? "pretty-naive" : "")}>{pretty(a.opt)}</div>
                  <div className="meta">{size(a.ast)} → {size(a.opt)} nodes{pretty(a.opt) === pretty(a.ast) ? " · unchanged" : ""}</div>
                  <p className="note">
                    {naive
                      ? <>The <code>optimizeNaive</code> rules — <code>x + 0 → x</code>, <code>x * 0 → 0</code>, … — with no side conditions. It has no theorem. <code>core.dfy</code> proves a counterexample against it.</>
                      : <>Same rules, guarded: identities rely on T1 (the operand is an integer); annihilation additionally requires the deleted operand to be division-free, so it cannot be hiding a crash.</>}
                  </p>
                </>
              ) : <div className="skipped">not reached</div>}
            </Stage>

            <Stage n={4} title="Compile" theorem="T3 correctness" muted={!a.code}>
              {a.code ? (
                <>
                  <Listing code={a.code} active={step > 0 ? step - 1 : null} />
                  <div className="meta">{instrCount(a.code)} instructions · structured branches, no jumps</div>
                </>
              ) : <div className="skipped">not reached</div>}
            </Stage>

            <Stage n={5} title="Run" muted={!a.trace}>
              {a.trace ? (
                <>
                  <div className="stepper">
                    <button onClick={() => { setPlaying(false); setStep(0) }} aria-label="Reset">⏮</button>
                    <button onClick={() => { setPlaying(false); setStep((s) => Math.max(0, s - 1)) }} aria-label="Step back">◂</button>
                    <button onClick={() => setPlaying((p) => !p)} aria-label={playing ? "Pause" : "Play"}>{playing ? "⏸" : "▶"}</button>
                    <button onClick={() => { setPlaying(false); setStep((s) => Math.min(nSteps, s + 1)) }} aria-label="Step forward">▸</button>
                    <input type="range" min={0} max={nSteps} value={step}
                           onChange={(e) => { setPlaying(false); setStep(Number(e.target.value)) }} aria-label="Step" />
                    <span className="meta">step {step}/{nSteps}</span>
                  </div>
                  <MachineState o={a.trace[Math.min(step, a.trace.length - 1)]} />
                  <p className="note">Every state shown is the output of the verified <code>run</code> on a prefix of the bytecode. There is no separate "display" machine.</p>
                </>
              ) : <div className="skipped">not reached</div>}
            </Stage>
          </div>

          <section className={"verdict " + (agree === null ? "verdict-none" : agree ? "verdict-ok" : "verdict-bad")}>
            <div className="verdict-cell">
              <div className="verdict-label">interpreter says</div>
              <div className="verdict-value">{prettyResult(a.ref)}</div>
              <div className="verdict-sub"><code>evaluate(e, [])</code> — the reference semantics</div>
            </div>
            <div className="verdict-mid">
              {agree === null ? "—" : agree ? "=" : "≠"}
            </div>
            <div className="verdict-cell">
              <div className="verdict-label">{naive ? "machine (naive optimizer) says" : "machine says"}</div>
              <div className="verdict-value">{a.machine ? prettyResult(a.machine) : "rejected by the type checker"}</div>
              <div className="verdict-sub"><code>run(compile({naive ? "optimizeNaive" : "optimize"}(e)), [], [])</code></div>
            </div>
            <div className="verdict-msg">
              {agree === null && <>The type checker refused this program, so nothing was compiled. T4 only promises agreement for well-typed programs.</>}
              {agree === true && !naive && <>Agreement is not luck: <strong>T4</strong> proves <code>runPipeline(e) === evaluate(e, [])</code> for <em>every</em> well-typed program, and this is one of them.</>}
              {agree === true && naive && <>They agree on <em>this</em> program. The naive optimizer has no theorem though — try <em>The trap</em>.</>}
              {agree === false && <><strong>Miscompiled.</strong> The naive optimizer turned a crash into an answer. This is exactly the program <code>NaiveMulZero</code> in <code>core.dfy</code> proves wrong — and the reason the verified optimizer's annihilation rule demands a division-free operand.</>}
            </div>
          </section>
        </>
      )}

      <section className="theorems">
        <div className="theorems-head">
          <h2>The four theorems</h2>
          <p>Specifications are <code>//@</code> comments on ordinary TypeScript functions; the text below is extracted from <code>core.ts</code> verbatim. Each one is a lemma discharged by Dafny in <code>core.dfy</code>.</p>
          <button className="linkish" onClick={() => setShowProofs((s) => !s)}>{showProofs ? "hide" : "show"} the specs</button>
        </div>
        <div className="theorem-grid">
          <article className="theorem">
            <h3><span className="theorem-tag">T1</span> Type soundness — <code>typeOf</code></h3>
            <p>If the checker accepts <code>e</code> at type <code>t</code>, then in every environment matching the typing environment, evaluating <code>e</code> yields a value of type <code>t</code> or fails with division by zero. Never an unbound variable, never a type error.</p>
            {showProofs && <Spec fn="typeOf" />}
          </article>
          <article className="theorem">
            <h3><span className="theorem-tag">T2</span> Optimizer soundness — <code>optimize</code></h3>
            <p>For every well-typed program: the optimized program is no larger, has the same type, and means exactly the same thing in every matching environment — the same value, or the same fault.</p>
            {showProofs && <Spec fn="optimize" />}
          </article>
          <article className="theorem">
            <h3><span className="theorem-tag">T3</span> Compiler correctness — <code>compile</code></h3>
            <p>For every program, typed or not, and every starting stack and environment: if the interpreter says the program is the value <code>v</code>, the machine halts with <code>v</code> pushed and the environment unchanged; if the interpreter says fault <code>f</code>, the machine crashes with exactly <code>f</code>.</p>
            {showProofs && <Spec fn="compile" />}
          </article>
          <article className="theorem">
            <h3><span className="theorem-tag">T4</span> The pipeline — <code>runPipeline</code></h3>
            <p>Typecheck, optimize, compile, run: for every well-typed closed program, the answer that comes out of the machine is exactly what the reference interpreter says.</p>
            {showProofs && <Spec fn="runPipeline" />}
          </article>
        </div>

        <h2>Three things the prover would not let us write</h2>
        <div className="theorem-grid">
          <article className="theorem counter">
            <h3><code>x * 0 → 0</code>, unguarded</h3>
            <p><code>(1 / 0) * 0</code> is well-typed and means <em>division by zero</em>. Deleting the left operand turns the crash into <code>0</code>. Fix: only delete a division-free operand — by T1 it then cannot fail. Proved as <code>NaiveMulZero</code>.</p>
          </article>
          <article className="theorem counter">
            <h3><code>x + 0 → x</code>, without types</h3>
            <p><code>true + 0</code> means <em>type error</em>; <code>true</code> means <code>true</code>. The identity is only sound when <code>x</code> is an integer — which is what the type checker, via T1, guarantees. This is why T2 assumes a well-typed program. Proved as <code>IdentityNeedsTypes</code>.</p>
          </article>
          <article className="theorem counter">
            <h3>Popping operands in the wrong order</h3>
            <p>Swap the two lines under <code>Prim</code> in <code>run</code> so the top of the stack is the <em>left</em> operand, and T3 fails: <code>3 - 1</code> compiles to a program that computes <code>-2</code>. The prover reports it in seconds; a test suite only does if someone thought to try subtraction.</p>
          </article>
        </div>
      </section>

      <footer className="foot">
        <p>
          <strong>What is not verified:</strong> this page (React), the parser and pretty-printer in <code>syntax.ts</code>, and the fact that JavaScript numbers are doubles while the proof reasons about mathematical integers (exact below 2<sup>53</sup>). The meaning of a program — <code>evaluate</code> — is the specification; everything else is proven against it.
        </p>
        <p>
          A <a href="https://github.com/midspiral/LemmaScript">LemmaScript</a> case study ·{" "}
          <a href="https://github.com/midspiral/optimist-lemmascript">source, proofs, and tutorial</a>
        </p>
      </footer>
    </div>
  )
}
