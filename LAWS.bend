import Base
import ./model.bend as Model
import ./optimizer.bend as Optimizer

law preserves_meaning:
  for +expr: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.optimize(expr), env) == Model.eval(expr, env) : Bool}

law keeps_variables:
  for +name: String
  {Optimizer.optimize(Model.Var{name}) == Model.Var{name} : Model.Expr}

law keeps_literals:
  for +value: Bool
  {Optimizer.optimize(Model.Lit{value}) == Model.Lit{value} : Model.Expr}

law removes_double_not:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Not{Model.Not{expr}}) == Optimizer.optimize(expr) : Model.Expr}

law folds_not_true:
  {Optimizer.optimize(Model.Not{Model.Lit{True{}}}) == Model.Lit{False{}} : Model.Expr}

law folds_not_false:
  {Optimizer.optimize(Model.Not{Model.Lit{False{}}}) == Model.Lit{True{}} : Model.Expr}

law simplifies_and_true:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.And{Model.Lit{True{}}, expr}) == Optimizer.optimize(expr) : Model.Expr}

law simplifies_and_false:
  for expr: Model.Expr
  {Optimizer.optimize(Model.And{Model.Lit{False{}}, expr}) == Model.Lit{False{}} : Model.Expr}

law simplifies_or_false:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Or{Model.Lit{False{}}, expr}) == Optimizer.optimize(expr) : Model.Expr}

law simplifies_or_true:
  for expr: Model.Expr
  {Optimizer.optimize(Model.Or{Model.Lit{True{}}, expr}) == Model.Lit{True{}} : Model.Expr}

law simplifies_and_true_right:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.And{expr, Model.Lit{True{}}}) == Optimizer.optimize(expr) : Model.Expr}

law simplifies_and_false_right:
  for expr: Model.Expr
  {Optimizer.optimize(Model.And{expr, Model.Lit{False{}}}) == Model.Lit{False{}} : Model.Expr}

law simplifies_or_false_right:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Or{expr, Model.Lit{False{}}}) == Optimizer.optimize(expr) : Model.Expr}

law simplifies_or_true_right:
  for expr: Model.Expr
  {Optimizer.optimize(Model.Or{expr, Model.Lit{True{}}}) == Model.Lit{True{}} : Model.Expr}

law de_morgan_and:
  for +left: Model.Expr
  for +right: Model.Expr
  {Optimizer.optimize(Model.Not{Model.And{left, right}}) == Optimizer.optimize(Model.Or{Model.Not{left}, Model.Not{right}}) : Model.Expr}

law de_morgan_or:
  for +left: Model.Expr
  for +right: Model.Expr
  {Optimizer.optimize(Model.Not{Model.Or{left, right}}) == Optimizer.optimize(Model.And{Model.Not{left}, Model.Not{right}}) : Model.Expr}

law removes_contradiction:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.And{expr, Model.Not{expr}}) == Model.Lit{False{}} : Model.Expr}

law removes_excluded_middle:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Or{expr, Model.Not{expr}}) == Model.Lit{True{}} : Model.Expr}

law and_idempotent:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.And{expr, expr}) == Optimizer.optimize(expr) : Model.Expr}

law or_idempotent:
  for +expr: Model.Expr
  {Optimizer.optimize(Model.Or{expr, expr}) == Optimizer.optimize(expr) : Model.Expr}

law absorbs_and_in_or:
  for +left: Model.Expr
  for +right: Model.Expr
  {Optimizer.optimize(Model.Or{left, Model.And{left, right}}) == Optimizer.optimize(left) : Model.Expr}

law absorbs_or_in_and:
  for +left: Model.Expr
  for +right: Model.Expr
  {Optimizer.optimize(Model.And{left, Model.Or{left, right}}) == Optimizer.optimize(left) : Model.Expr}
