import Base
import ./model.bend as Model

def same(a: Model.Expr, b: Model.Expr) -> Bool:
  match a b:
    case Model.Lit{x} Model.Lit{y}:
      Bool.not(Bool.xor(x, y))
    case Model.Var{x} Model.Var{y}:
      String.eq(x, y)
    case Model.Not{x} Model.Not{y}:
      same(x, y)
    case Model.And{al, ar} Model.And{bl, br}:
      l r = same(al, bl) same(ar, br)
      Bool.and(l, r)
    case Model.Or{al, ar} Model.Or{bl, br}:
      l r = same(al, bl) same(ar, br)
      Bool.and(l, r)
    case _ _:
      False{}

def negate(expr: Model.Expr) -> Model.Expr:
  match expr:
    case Model.Lit{value}:
      Model.Lit{Bool.not(value)}
    case Model.Var{name}:
      Model.Not{Model.Var{name}}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          Model.Not{Model.Lit{Bool.not(value)}}
        case Model.Var{name}:
          Model.Var{name}
        case Model.Not{x}:
          Model.Not{Model.Not{negate(x)}}
        case Model.And{left, right}:
          l r = negate(left) negate(right)
          Model.Not{Model.Or{l, r}}
        case Model.Or{left, right}:
          l r = negate(left) negate(right)
          Model.Not{Model.And{l, r}}
    case Model.And{left, right}:
      l r = negate(left) negate(right)
      Model.Or{l, r}
    case Model.Or{left, right}:
      l r = negate(left) negate(right)
      Model.And{l, r}

def implies(+left: Model.Expr, +right: Model.Expr) -> Bool:
  match right:
    case Model.Or{x, y}:
      a b = same(left, Model.Or{x, y}) same(left, x)
      Bool.or(a, b)
    case other:
      same(left, other)

def implied(+left: Model.Expr, +right: Model.Expr) -> Bool:
  match right:
    case Model.And{x, y}:
      a b = same(left, Model.And{x, y}) same(left, x)
      Bool.or(a, b)
    case other:
      same(left, other)

def both_right(+left: Model.Expr, +right: Model.Expr) -> Model.Expr:
  match right:
    case Model.Lit{True{}}:
      left
    case Model.Lit{False{}}:
      Model.Lit{False{}}
    case other:
      complement absorbed = same(negate(left), other) implies(left, other)
      Bool.pick(Model.Expr, complement, Model.Lit{False{}}, Bool.pick(Model.Expr, absorbed, left, Model.And{left, other}))

def both(left: Model.Expr, +right: Model.Expr) -> Model.Expr:
  match left:
    case Model.Lit{True{}}:
      right
    case Model.Lit{False{}}:
      Model.Lit{False{}}
    case other:
      both_right(other, right)

def either_right(+left: Model.Expr, +right: Model.Expr) -> Model.Expr:
  match right:
    case Model.Lit{True{}}:
      Model.Lit{True{}}
    case Model.Lit{False{}}:
      left
    case other:
      complement absorbed = same(negate(left), other) implied(left, other)
      Bool.pick(Model.Expr, complement, Model.Lit{True{}}, Bool.pick(Model.Expr, absorbed, left, Model.Or{left, other}))

def either(left: Model.Expr, +right: Model.Expr) -> Model.Expr:
  match left:
    case Model.Lit{True{}}:
      Model.Lit{True{}}
    case Model.Lit{False{}}:
      right
    case other:
      either_right(other, right)

def optimize(expr: Model.Expr) -> Model.Expr:
  match expr:
    case Model.Lit{value}:
      Model.Lit{value}
    case Model.Var{name}:
      Model.Var{name}
    case Model.Not{inner}:
      negate(optimize(inner))
    case Model.And{left, right}:
      l r = optimize(left) optimize(right)
      both(l, r)
    case Model.Or{left, right}:
      l r = optimize(left) optimize(right)
      either(l, r)
