import Base
import ./model.bend as Model

def cat(xs: List<&2, String>, ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> cat(t, ys)

def vars(expr: Model.Expr) -> List<&2, String>:
  match expr:
    case Model.Lit{value}:
      Nil{}
    case Model.Var{name}:
      name <> Nil{}
    case Model.Not{inner}:
      vars(inner)
    case Model.And{left, right}:
      l r = vars(left) vars(right)
      cat(l, r)
    case Model.Or{left, right}:
      l r = vars(left) vars(right)
      cat(l, r)

def mem(+name: String, names: List<&2, String>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(String.eq(name, h), mem(name, t))

def uniq.if(+name: String, skip: Unit -> List<&2, String>, keep: Unit -> List<&2, String>, seen: Bool) -> List<&2, String>:
  match seen:
    case False{}:
      name <> keep(Unit{})
    case True{}:
      skip(Unit{})

def uniq(names: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match names:
    case Nil{}:
      Nil{}
    case +h <> +t:
      uniq.if(h, u => uniq(t, seen), u => uniq(t, h <> seen), mem(h, seen))

def agree(names: List<&2, String>, +env: Model.Env, +a: Model.Expr, +b: Model.Expr) -> Bool:
  match names:
    case Nil{}:
      Bool.not(Bool.xor(Model.eval(a, env), Model.eval(b, env)))
    case +h <> +t:
      x y = agree(t, Model.EnvCons{h, True{}, env}, a, b) agree(t, Model.EnvCons{h, False{}, env}, a, b)
      Bool.and(x, y)

def ecat(xs: List<&2, Model.Expr>, ys: List<&2, Model.Expr>) -> List<&2, Model.Expr>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> ecat(t, ys)

def nots(xs: List<&2, Model.Expr>) -> List<&2, Model.Expr>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Model.Not{h} <> nots(t)

def mk(op: Bool, left: Model.Expr, right: Model.Expr) -> Model.Expr:
  match op:
    case False{}:
      Model.And{left, right}
    case True{}:
      Model.Or{left, right}

def pairs(+op: Bool, +left: Model.Expr, rights: List<&2, Model.Expr>) -> List<&2, Model.Expr>:
  match rights:
    case Nil{}:
      Nil{}
    case h <> t:
      mk(op, left, h) <> pairs(op, left, t)

def prod(+op: Bool, lefts: List<&2, Model.Expr>, +rights: List<&2, Model.Expr>) -> List<&2, Model.Expr>:
  match lefts:
    case Nil{}:
      Nil{}
    case h <> t:
      ecat(pairs(op, h, rights), prod(op, t, rights))

def leaves(names: List<&2, String>) -> List<&2, Model.Expr>:
  match names:
    case Nil{}:
      Nil{}
    case h <> t:
      Model.Var{h} <> leaves(t)

def atoms(r: Nat, names: List<&2, String>) -> List<&2, Model.Expr>:
  match r:
    case 0n:
      leaves(names)
    case 1n+p:
      Nil{}

def cands(+fuel: Nat, +s: Nat, split: Bool, +i: Nat, +names: List<&2, String>) -> List<&2, Model.Expr>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+h:
      match s:
        case 0n:
          Nil{}
        case 1n+r:
          match split:
            case False{}:
              a b = cands(h, r, False{}, 0n, names) cands(1n+h, r, True{}, 1n, names)
              ecat(atoms(r, names), ecat(nots(a), b))
            case True{}:
              +l +rs = cands(h, i, False{}, 0n, names) cands(h, 1n+r, False{}, 0n, names)
              ecat(prod(False{}, l, rs), ecat(prod(True{}, l, rs), cands(1n+h, r, True{}, 1n+i, names)))

def level(+n: Nat, +names: List<&2, String>) -> List<&2, Model.Expr>:
  cands(n, n, False{}, 0n, names)

def find.if(+head: Model.Expr, rest: Unit -> Maybe<&2, Model.Expr>, hit: Bool) -> Maybe<&2, Model.Expr>:
  match hit:
    case False{}:
      rest(Unit{})
    case True{}:
      Some{head}

def find(xs: List<&2, Model.Expr>, +names: List<&2, String>, +target: Model.Expr) -> Maybe<&2, Model.Expr>:
  match xs:
    case Nil{}:
      None{}
    case +h <> t:
      find.if(h, u => find(t, names, target), agree(names, Model.EnvNil{}, h, target))

def search.if(rest: Unit -> Model.Expr, found: Maybe<&2, Model.Expr>) -> Model.Expr:
  match found:
    case None{}:
      rest(Unit{})
    case Some{x}:
      x

def search(fuel: Nat, +n: Nat, +names: List<&2, String>, +target: Model.Expr) -> Model.Expr:
  match fuel:
    case 0n:
      target
    case 1n+f:
      search.if(u => search(f, 1n+n, names, target), find(level(n, names), names, target))

def lits() -> List<&2, Model.Expr>:
  Model.Lit{False{}} <> Model.Lit{True{}} <> Nil{}

def optimize(+expr: Model.Expr) -> Model.Expr:
  +names = uniq(vars(expr), Nil{})
  search.if(u => search(Model.len(expr), 1n, names, expr), find(lits(), names, expr))
