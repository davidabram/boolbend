import Base
import ./model.bend as Model
import ./optimizer.bend as Optimizer

type Example is Data:
  Example{id: Nat, title: String, expr: Model.Expr}

def t() -> Model.Expr:
  Model.Lit{True{}}

def f() -> Model.Expr:
  Model.Lit{False{}}

def v(name: String) -> Model.Expr:
  Model.Var{name}

def no(inner: Model.Expr) -> Model.Expr:
  Model.Not{inner}

def an(left: Model.Expr, right: Model.Expr) -> Model.Expr:
  Model.And{left, right}

def or(left: Model.Expr, right: Model.Expr) -> Model.Expr:
  Model.Or{left, right}

# Wraps an expression in n nots.
def nots(+n: Nat, inner: Model.Expr) -> Model.Expr:
  match n:
    case 0n:
      inner
    case 1n+p:
      no(nots(p, inner))

# A balanced or-tree of 2^depth copies of a leaf, built in parallel.
def tree(+depth: Nat, +leaf: Model.Expr) -> Model.Expr:
  match depth:
    case 0n:
      leaf
    case 1n+p:
      l r = tree(p, leaf) tree(p, leaf)
      or(l, r)

# Ordered from a single leaf up to deep expressions that use every rewrite,
# then edge cases: all-literal input, odd names, deep or wide shapes, and
# inputs whose smallest form no local rewrite reaches.
def examples() -> List<&2, Example>:
  [
    Example{1n, "literal", t()},
    Example{2n, "variable", v("a")},
    Example{3n, "not true", no(t())},
    Example{4n, "not false", no(f())},
    Example{5n, "double not", no(no(v("a")))},
    Example{6n, "triple not", no(no(no(v("a"))))},
    Example{7n, "true and a", an(t(), v("a"))},
    Example{8n, "false and a", an(f(), v("a"))},
    Example{9n, "false or a", or(f(), v("a"))},
    Example{10n, "true or a", or(t(), v("a"))},
    Example{11n, "nothing to simplify", an(v("a"), or(v("b"), no(v("c"))))},
    Example{12n, "literal on the right folds", an(v("a"), t())},
    Example{13n, "constants fold through not", no(an(t(), f()))},
    Example{14n, "dead branch of an or", or(an(f(), v("a")), an(t(), v("b")))},
    Example{15n, "rewrites in both operands", an(no(no(v("a"))), or(f(), v("b")))},
    Example{16n, "not cancels after folding", no(or(f(), no(v("a"))))},
    Example{17n, "folded left decides the and", an(no(or(f(), t())), or(v("a"), no(v("b"))))},
    Example{18n, "nested identities", or(an(t(), or(f(), an(t(), v("a")))), an(no(t()), v("b")))},
    Example{19n, "four variables", an(or(an(t(), v("a")), no(no(v("b")))), or(an(f(), v("c")), no(no(no(v("d"))))))},
    Example{20n, "everything at once", no(no(or(an(no(f()), or(an(no(no(t())), no(no(v("a")))), an(f(), v("b")))), no(or(no(t()), an(or(f(), no(no(v("c")))), an(no(f()), no(no(no(v("d")))))))))))},
    Example{21n, "all literals, and", an(t(), t())},
    Example{22n, "all literals, or", or(f(), f())},
    Example{23n, "empty variable name", no(v(""))},
    Example{24n, "variable missing from env", an(v("e"), v("a"))},
    Example{25n, "names are case sensitive", or(v("A"), v("a"))},
    Example{26n, "variable named like a literal", an(v("True"), v("a"))},
    Example{27n, "variable named like an operator", no(v("!a"))},
    Example{28n, "non-ascii variable name", no(no(v("é")))},
    Example{29n, "contradiction", an(v("a"), no(v("a")))},
    Example{30n, "excluded middle", or(v("a"), no(v("a")))},
    Example{31n, "idempotent and", an(v("a"), v("a"))},
    Example{32n, "absorption", or(v("a"), an(v("a"), v("b")))},
    Example{33n, "not of an and is already smallest", no(an(v("a"), v("b")))},
    Example{34n, "not of a wider and is already smallest", no(an(an(v("a"), v("b")), an(v("c"), v("d"))))},
    Example{35n, "not of a folded or", no(or(v("a"), t()))},
    Example{36n, "not of a folded and", no(an(v("a"), f()))},
    Example{37n, "101 nots on a variable", nots(101n, v("a"))},
    Example{38n, "100 nots on an and", nots(100n, an(v("a"), v("b")))},
    Example{39n, "same or, grouped two ways", an(or(or(v("a"), v("b")), v("c")), or(v("a"), or(v("b"), v("c"))))},
    Example{40n, "wide tree of dead leaves", tree(4n, an(f(), v("a")))},
    Example{41n, "and of nots becomes a nor", an(no(v("a")), no(v("b")))},
    Example{42n, "common factor pulled out", or(an(v("a"), v("b")), an(v("a"), v("c")))},
    Example{43n, "consensus term dropped", or(or(an(v("a"), v("b")), an(no(v("a")), v("c"))), an(v("b"), v("c")))},
    Example{44n, "xor saves one not", or(an(v("a"), no(v("b"))), an(no(v("a")), v("b")))},
  ]

def show(expr: Model.Expr) -> String:
  match expr:
    case Model.Lit{value}:
      Bool.show(value)
    case Model.Var{name}:
      name
    case Model.Not{inner}:
      "!" ++ show(inner)
    case Model.And{left, right}:
      "(" ++ show(left) ++ " & " ++ show(right) ++ ")"
    case Model.Or{left, right}:
      "(" ++ show(left) ++ " | " ++ show(right) ++ ")"

def size(expr: Model.Expr) -> Nat:
  match expr:
    case Model.Lit{value}:
      1n
    case Model.Var{name}:
      1n
    case Model.Not{inner}:
      1n+size(inner)
    case Model.And{left, right}:
      l r = size(left) size(right)
      1n+Nat.add(l, r)
    case Model.Or{left, right}:
      l r = size(left) size(right)
      1n+Nat.add(l, r)

def bind(+name: String, value: Bool, env: Model.Env) -> Model.Env:
  Model.EnvCons{name, value, env}

def env_of(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> Model.Env:
  bind("a", a, bind("b", b, bind("c", c, bind("d", d, Model.EnvNil{}))))

# Every assignment of a, b, c and d: 16 environments.
def envs() -> List<&2, Model.Env>:
  [
    env_of(False{}, False{}, False{}, False{}),
    env_of(False{}, False{}, False{}, True{}),
    env_of(False{}, False{}, True{}, False{}),
    env_of(False{}, False{}, True{}, True{}),
    env_of(False{}, True{}, False{}, False{}),
    env_of(False{}, True{}, False{}, True{}),
    env_of(False{}, True{}, True{}, False{}),
    env_of(False{}, True{}, True{}, True{}),
    env_of(True{}, False{}, False{}, False{}),
    env_of(True{}, False{}, False{}, True{}),
    env_of(True{}, False{}, True{}, False{}),
    env_of(True{}, False{}, True{}, True{}),
    env_of(True{}, True{}, False{}, False{}),
    env_of(True{}, True{}, False{}, True{}),
    env_of(True{}, True{}, True{}, False{}),
    env_of(True{}, True{}, True{}, True{}),
  ]

def same(a: Bool, b: Bool) -> Nat:
  Bool.pick(Nat, Bool.not(Bool.xor(a, b)), 1n, 0n)

# Counts the environments where both expressions evaluate alike.
def agreements(xs: List<&2, Model.Env>, +before: Model.Expr, +after: Model.Expr) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+env, rest}:
      Nat.add(same(Model.eval(before, env), Model.eval(after, env)), agreements(rest, before, after))

def report(example: Example) -> String:
  Example{id, title, expr} = example
  +expr = expr
  +after = Optimizer.optimize(expr)
  String.concat([
    "#", Nat.show(id), " ", title, "\n",
    "  in : ", show(expr), "\n",
    "  out: ", show(after), "\n",
    "  size ", Nat.show(size(expr)), " -> ", Nat.show(size(after)),
    ", agrees on ", Nat.show(agreements(envs(), expr, after)), "/16 environments\n",
  ])

def report_all(xs: List<&2, Example>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{example, rest}:
      report(example) ++ report_all(rest)

# Splits the list in half at each level, so the examples fan out across cores.
def render(+depth: Nat, xs: List<&2, Example>) -> String:
  match depth:
    case 0n:
      report_all(xs)
    case 1n+p:
      +xs = xs
      +half = Nat.div(List.length(&2, Example, xs), 2n)
      a b = render(p, List.take(&2, Example, xs, half)) render(p, List.drop(&2, Example, xs, half))
      a ++ b

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(render(5n, examples()))
