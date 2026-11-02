import Base

type Expr is Data:
  Lit{value: Bool}
  Var{name: String}
  Not{inner: Expr}
  And{left: Expr, right: Expr}
  Or{left: Expr, right: Expr}

type Env is Data:
  EnvNil{}
  EnvCons{name: String, value: Bool, rest: Env}

def lookup(env: Env, +name: String) -> Bool:
  match env:
    case EnvNil{}:
      False{}
    case EnvCons{bound_name, value, rest}:
      Bool.pick(Bool, String.eq(name, bound_name), value, lookup(rest, name))

def eval(expr: Expr, +env: Env) -> Bool:
  match expr:
    case Lit{value}:
      value
    case Var{name}:
      lookup(env, name)
    case Not{inner}:
      Bool.not(eval(inner, env))
    case And{left, right}:
      Bool.and(eval(left, env), eval(right, env))
    case Or{left, right}:
      Bool.or(eval(left, env), eval(right, env))

