# bendworld

Hey Aron 👋

You spend your days telling people to write the theorem first and let the
machine keep them honest. This repo does that for a small, ordinary program, a
boolean expression optimizer, written in [Bend 2](https://github.com/bendlang/bend).
Every rewrite it makes has a proof, and a kernel that is itself verified in Lean
re-checks those proofs. Please don't unfollow me yet.

## What it is

A tiny compiler pass. Take a boolean expression like

```
!!((!False & ((!!True & !!a) | (False & b))) | !(!True | ((False | !!c) & (!False & !!!d))))
```

and shrink it to

```
(a | (!c | d))
```

without changing what it means. The optimizer folds constants, removes double
negations, pushes `!` inward (De Morgan), and handles contradiction
(`a & !a`), excluded middle (`a | !a`), idempotence and absorption.

Inside `optimizer.bend`, the left and right halves of an expression are optimized
in parallel (`l r = optimize(left) optimize(right)`), so on a big tree the work
spreads across your cores. Bend makes it look that easy.

## Who wrote what

This is the part I actually want you to look at. The project is split along the
line Bend calls *law-driven development*:

| File | Written by | What it is |
|---|---|---|
| `model.bend` | **a hu-man** | The spec of the world: the `Expr` syntax tree, variable environments, and `eval`, which says what an expression *means*. |
| `LAWS.bend` | **a hu-man** | 22 laws. These are the theorem statements. The AI is not allowed to touch them. |
| `optimizer.bend` | the AI | The implementation. |
| `PROOF.bend` | the AI | A proof of every law in `LAWS.bend`, plus whatever helper lemmas it needed. |
| `demo.bend` | the AI | 40 example inputs, each run through the optimizer and compared against the original. |

So the human wrote two short files: the semantics and the theorem statements.
The AI wrote everything else, and it can't fake any of it, because
`bend PROOF.bend` fails until every law is proven.

### How the model is written

`model.bend` is deliberately boring. It's the reference semantics, the thing
you'd trust without proofs because it's too small to get wrong:

```python
type Expr is Data:
  Lit{value: Bool}
  Var{name: String}
  Not{inner: Expr}
  And{left: Expr, right: Expr}
  Or{left: Expr, right: Expr}

def eval(expr: Expr, +env: Env) -> Bool:
  match expr:
    case Lit{value}: value
    case Var{name}:  lookup(env, name)
    case Not{inner}: Bool.not(eval(inner, env))
    ...
```

There's no cleverness in it. It's a definitional interpreter, the same thing
you'd write as an inductive type plus a structural `def` in Lean.

### How the laws are written

A Bend `law` is a proposition. If you squint, it's a Lean `theorem` statement
with no `:= by ...` after it. The headline law is the one any compiler person
wants:

```python
law preserves_meaning:
  for +expr: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.optimize(expr), env) == Model.eval(expr, env) : Bool}
```

In Lean that's roughly
`theorem preserves_meaning (e : Expr) (env : Env) : eval (optimize e) env = eval e env`.

That law alone would allow a do-nothing optimizer (`optimize e = e` satisfies it
trivially), so the other 21 laws say what the optimizer must actually *do*:

```python
law removes_double_not:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Not{Model.Not{expr}}) == Optimizer.optimize(expr) : Model.Expr}

law removes_contradiction:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.And{expr, Model.Not{expr}}) == Model.Lit{False{}} : Model.Expr}
```

Correctness laws plus behaviour laws give a spec that's tight from both sides.

### How the proofs look

Bend has no tactics. A proposition is a type and a proof is a `def` of that
type: pure term mode. `{==}` is `rfl`, `match` is case analysis that refines the
goal, a recursive call is the induction hypothesis, and `%e : P` rewrites. Each
law `foo` in `LAWS.bend` gets proven by `def Laws.foo` in `PROOF.bend`:

```python
def Laws.removes_contradiction(expr):
  both_complement(Optimizer.optimize(expr))
```

`PROOF.bend` is about 2,000 lines and 100+ lemmas. Nobody has to read it,
because the checker already did. You read the 22 laws.

## How to run it

### 1. Get Bend (and the right Lean)

With Nix and direnv:

```sh
direnv allow        # or: nix develop
```

The dev shell gives you `bend` and `elan`, pinned to
`leanprover/lean4:v4.34.0`. That's the exact Lean version `--verdict` needs. Yes,
Aron, there's a Lean toolchain in here. You're welcome.

Without Nix, install Bend from <https://github.com/bendlang/bend> and run
`bend guide` to learn the language.

### 2. Check the proofs

```sh
bend PROOF.bend
```

```
ALL PROOFS CHECK
```

If a law is open or false, this prints `SOME PROOFS FAIL` and names it. This is
the gate: run it before every commit.

### 3. Check them again, with a verified kernel

```sh
bend PROOF.bend --verdict
```

This re-checks every proof with BendTT, a small kernel whose soundness is proven
in Lean (no def it accepts has type `Empty`). It only passes if none of the code
outside Base is `@unsafe` or foreign. The trust story ends up close to the one
you know: a small kernel you can audit, with a machine-checked metatheory.

### 4. Watch it optimize

```sh
bend demo.bend
```

```
#20 everything at once
  in : !!((!False & ((!!True & !!a) | (False & b))) | !(!True | ((False | !!c) & (!False & !!!d))))
  out: (a | (!c | d))
  size 34 -> 6, agrees on 16/16 environments
...
#33 de morgan grows the output
  in : !(a & b)
  out: (!a | !b)
  size 4 -> 5, agrees on 16/16 environments
```

The demo runs 40 examples, from a single literal up to a 101-deep stack of `!`
and wide trees, and checks each result against all 16 assignments of
`a, b, c, d`. That's a sanity check for humans. The real guarantee is the proof
of `preserves_meaning`.

Some examples are there on purpose to show what the optimizer *won't* do. It
doesn't normalize associativity (#39), and De Morgan can make the output bigger
(#33, #34). If you want those properties, add a law. That's the whole workflow.

## The pitch, in one paragraph

Lean folks already know that a precise statement is worth more than a thousand
lines of implementation. Bend takes that and points it at everyday code
written with AI: the human writes the model and the laws, the AI writes the code
and the proofs, and the checker decides who's right. No vibes and no "looks good
to me". `ALL PROOFS CHECK` or it didn't happen.

## Rules for contributors (human or otherwise)

- `LAWS.bend` and `model.bend` belong to the humans. Change them on purpose,
  never to make a proof go through.
- Run `bend PROOF.bend` before committing.
- Parallelize wherever you can. Bend will happily use every core you have.
