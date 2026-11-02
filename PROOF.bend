import Base
import ./model.bend as Model
import ./optimizer.bend as Optimizer
import ./LAWS.bend as Laws

law bool_not_not:
  for b: Bool
  {Bool.not(Bool.not(b)) == b : Bool}

def bool_not_not(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_and_true:
  for b: Bool
  {Bool.and(b, True{}) == b : Bool}

def bool_and_true(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_and_false:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def bool_and_false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_true:
  for b: Bool
  {Bool.or(b, True{}) == True{} : Bool}

def bool_or_true(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_false:
  for b: Bool
  {Bool.or(b, False{}) == b : Bool}

def bool_or_false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_not:
  for a: Bool
  for b: Bool
  {Bool.or(Bool.not(a), Bool.not(b)) == Bool.not(Bool.and(a, b)) : Bool}

def bool_or_not(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_and_not:
  for a: Bool
  for b: Bool
  {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}

def bool_and_not(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law both_true_right:
  for left: Model.Expr
  {Optimizer.both(left, Model.Lit{True{}}) == left : Model.Expr}

def both_true_right(left):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law both_false_right:
  for left: Model.Expr
  {Optimizer.both(left, Model.Lit{False{}}) == Model.Lit{False{}} : Model.Expr}

def both_false_right(left):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law either_true_right:
  for left: Model.Expr
  {Optimizer.either(left, Model.Lit{True{}}) == Model.Lit{True{}} : Model.Expr}

def either_true_right(left):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law either_false_right:
  for left: Model.Expr
  {Optimizer.either(left, Model.Lit{False{}}) == left : Model.Expr}

def either_false_right(left):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law bool_and_self:
  for b: Bool
  {Bool.and(b, b) == b : Bool}

def bool_and_self(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_self:
  for b: Bool
  {Bool.or(b, b) == b : Bool}

def bool_or_self(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_and_or:
  for a: Bool
  for b: Bool
  {Bool.and(a, Bool.or(a, b)) == a : Bool}

def bool_and_or(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_and:
  for a: Bool
  for b: Bool
  {Bool.or(a, Bool.and(a, b)) == a : Bool}

def bool_or_and(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_and_not_self:
  for a: Bool
  {Bool.and(a, Bool.not(a)) == False{} : Bool}

def bool_and_not_self(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law bool_or_not_self:
  for a: Bool
  {Bool.or(a, Bool.not(a)) == True{} : Bool}

def bool_or_not_self(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law absurd:
  for -A: Type
  for e: Empty
  A

def absurd(A, e):
  match e:

def bool_disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law bool_clash:
  for e: {False{} == True{} : Bool}
  Empty

def bool_clash(e):
  %e : bool_disc(_)
  Unit{}

def cmp_disc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

law lt_clash:
  for e: {LT{} == EQ{} : Cmp}
  Empty

def lt_clash(e):
  %e : cmp_disc(_)
  Unit{}

law gt_clash:
  for e: {GT{} == EQ{} : Cmp}
  Empty

def gt_clash(e):
  %e : cmp_disc(_)
  Unit{}

law true_clash:
  for e: {True{} == False{} : Bool}
  Empty

def true_clash(e):
  bool_clash(Equal.sym(Bool, True{}, False{}, e))

law and_true_left:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_true_left(a, b, e):
  match a:
    case False{}:
      absurd({False{} == True{} : Bool}, bool_clash(e))
    case True{}:
      {==}

law and_true_right:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_true_right(a, b, e):
  match a:
    case False{}:
      absurd({b == True{} : Bool}, bool_clash(e))
    case True{}:
      e

law and_true:
  for a: Bool
  for b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_true(a, b, ea, eb):
  match a:
    case False{}:
      absurd({False{} == True{} : Bool}, bool_clash(ea))
    case True{}:
      eb

law and_false:
  for a: Bool
  for b: Bool
  for e: {a == False{} : Bool}
  {Bool.and(a, b) == False{} : Bool}

def and_false(a, b, e):
  match a:
    case False{}:
      {==}
    case True{}:
      absurd({b == False{} : Bool}, true_clash(e))

law or_true_left:
  for a: Bool
  for b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_true_left(a, b, e):
  match a:
    case False{}:
      absurd({b == True{} : Bool}, bool_clash(e))
    case True{}:
      {==}

law or_true_right:
  for a: Bool
  for b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_true_right(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      {==}

law bool_ext:
  for x: Bool
  for y: Bool
  for f: {x == True{} : Bool} -> {y == True{} : Bool}
  for g: {y == True{} : Bool} -> {x == True{} : Bool}
  {x == y : Bool}

def bool_ext(x, y, f, g):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({False{} == True{} : Bool}, bool_clash(g({==})))
    case True{} False{}:
      absurd({True{} == False{} : Bool}, bool_clash(f({==})))
    case True{} True{}:
      {==}

# Base's U32 is a plain bit vector, so String.eq can be taken apart down to bits.
law word_fin_refl:
  for b: Bool
  {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}

def word_fin_refl(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law word_cmp_refl:
  for +n: Nat
  for +w: Word(n)
  {EQ{} == Word.cmp(n, w, w) : Cmp}

def word_cmp_refl(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+h, +t}:
          %word_cmp_refl(p, t) : {EQ{} == Word.cmp.fin(h, h, _) : Cmp}
          Equal.sym(Cmp, Word.cmp.fin(h, h, EQ{}), EQ{}, word_fin_refl(h))

law word_fin_tail:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

def word_fin_tail(ab, bb, t, e):
  match t:
    case LT{}:
      absurd({LT{} == EQ{} : Cmp}, lt_clash(e))
    case EQ{}:
      {==}
    case GT{}:
      absurd({GT{} == EQ{} : Cmp}, gt_clash(e))

law bool_cmp_sound:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

def bool_cmp_sound(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({False{} == True{} : Bool}, lt_clash(e))
    case True{} False{}:
      absurd({True{} == False{} : Bool}, gt_clash(e))
    case True{} True{}:
      {==}

law word_fin_head:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {ab == bb : Bool}

def word_fin_head(ab, bb, t, e):
  match t:
    case LT{}:
      absurd({ab == bb : Bool}, lt_clash(e))
    case EQ{}:
      bool_cmp_sound(ab, bb, e)
    case GT{}:
      absurd({ab == bb : Bool}, gt_clash(e))

law word_cmp_sound:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def word_cmp_sound(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %word_fin_head(ah, bh, Word.cmp(p, at, bt), e) : {WCon{ah, at} == WCon{_, bt} : Word(1n+p)}
          %word_cmp_sound(p, at, bt, word_fin_tail(ah, bh, Word.cmp(p, at, bt), e)) : {WCon{ah, at} == WCon{ah, _} : Word(1n+p)}
          {==}

law u32_cmp_refl:
  for +x: U32
  {EQ{} == U32.cmp(x, x) : Cmp}

def u32_cmp_refl(x):
  match x:
    case U32{+w}:
      word_cmp_refl(32n, w)

law u32_cmp_sound:
  for +x: U32
  for +y: U32
  for e: {U32.cmp(x, y) == EQ{} : Cmp}
  {x == y : U32}

def u32_cmp_sound(x, y, e):
  match x y:
    case U32{+a} U32{+b}:
      %word_cmp_sound(32n, a, b, e) : {U32{a} == U32{_} : U32}
      {==}

law string_order_refl:
  for +s: String
  {String.order.go(s, s, EQ{}) == EQ{} : Cmp}

def string_order_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %u32_cmp_refl(x) : {String.order.go(t, t, _) == EQ{} : Cmp}
      string_order_refl(t)

law string_eq_refl:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

def string_eq_refl(s):
  %Equal.sym(Cmp, String.order.go(s, s, EQ{}), EQ{}, string_order_refl(s)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# A non-EQ prefix decides the order, so an EQ result means the prefix was EQ.
law string_order_prefix:
  for c: Cmp
  for a: String
  for b: String
  for e: {String.order.go(a, b, c) == EQ{} : Cmp}
  {c == EQ{} : Cmp}

def string_order_prefix(c, a, b, e):
  match c:
    case LT{}:
      match a b:
        case SNil{} SNil{}:
          absurd({LT{} == EQ{} : Cmp}, lt_clash(e))
        case SNil{} SCon{h, t}:
          absurd({LT{} == EQ{} : Cmp}, lt_clash(e))
        case SCon{h, t} SNil{}:
          absurd({LT{} == EQ{} : Cmp}, lt_clash(e))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          absurd({LT{} == EQ{} : Cmp}, lt_clash(e))
    case EQ{}:
      {==}
    case GT{}:
      match a b:
        case SNil{} SNil{}:
          absurd({GT{} == EQ{} : Cmp}, gt_clash(e))
        case SNil{} SCon{h, t}:
          absurd({GT{} == EQ{} : Cmp}, gt_clash(e))
        case SCon{h, t} SNil{}:
          absurd({GT{} == EQ{} : Cmp}, gt_clash(e))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          absurd({GT{} == EQ{} : Cmp}, gt_clash(e))

law string_order_step:
  for a: String
  for b: String
  for c: Cmp
  for head: {c == EQ{} : Cmp}
  for e: {String.order.go(a, b, c) == EQ{} : Cmp}
  {String.order.go(a, b, EQ{}) == EQ{} : Cmp}

def string_order_step(a, b, c, head, e):
  match c:
    case LT{}:
      absurd({String.order.go(a, b, EQ{}) == EQ{} : Cmp}, lt_clash(head))
    case EQ{}:
      e
    case GT{}:
      absurd({String.order.go(a, b, EQ{}) == EQ{} : Cmp}, gt_clash(head))

law string_order_sound:
  for +a: String
  for +b: String
  for +e: {String.order.go(a, b, EQ{}) == EQ{} : Cmp}
  {a == b : String}

def string_order_sound(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      absurd({SNil{} == SCon{h, t} : String}, lt_clash(e))
    case SCon{h, t} SNil{}:
      absurd({SCon{h, t} == SNil{} : String}, gt_clash(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      +head = string_order_prefix(U32.cmp(x, y), t1, t2, e)
      %u32_cmp_sound(x, y, head) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %string_order_sound(t1, t2, string_order_step(t1, t2, U32.cmp(x, y), head, e)) : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

law cmp_is_eq_true:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def cmp_is_eq_true(c, e):
  match c:
    case LT{}:
      absurd({LT{} == EQ{} : Cmp}, bool_clash(e))
    case EQ{}:
      {==}
    case GT{}:
      absurd({GT{} == EQ{} : Cmp}, bool_clash(e))

law string_eq_sound:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def string_eq_sound(a, b, e):
  string_order_sound(a, b, cmp_is_eq_true(String.order.go(a, b, EQ{}), e))

law same_refl:
  for +a: Model.Expr
  {Optimizer.same(a, a) == True{} : Bool}

def same_refl(a):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      string_eq_refl(name)
    case Model.Not{inner}:
      same_refl(inner)
    case Model.And{l, r}:
      and_true(Optimizer.same(l, l), Optimizer.same(r, r), same_refl(l), same_refl(r))
    case Model.Or{l, r}:
      and_true(Optimizer.same(l, l), Optimizer.same(r, r), same_refl(l), same_refl(r))

law lit_sound:
  for x: Bool
  for y: Bool
  for e: {Bool.not(Bool.xor(x, y)) == True{} : Bool}
  {Model.Lit{x} == Model.Lit{y} : Model.Expr}

def lit_sound(x, y, e):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({Model.Lit{False{}} == Model.Lit{True{}} : Model.Expr}, bool_clash(e))
    case True{} False{}:
      absurd({Model.Lit{True{}} == Model.Lit{False{}} : Model.Expr}, bool_clash(e))
    case True{} True{}:
      {==}

law same_sound:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {Optimizer.same(a, b) == True{} : Bool}
  {a == b : Model.Expr}

def same_sound(a, b, e):
  match a b:
    case Model.Lit{x} Model.Lit{y}:
      lit_sound(x, y, e)
    case Model.Var{x} Model.Var{y}:
      %string_eq_sound(x, y, e) : {Model.Var{x} == Model.Var{_} : Model.Expr}
      {==}
    case Model.Not{x} Model.Not{y}:
      %same_sound(x, y, e) : {Model.Not{x} == Model.Not{_} : Model.Expr}
      {==}
    case Model.And{al, ar} Model.And{bl, br}:
      %same_sound(al, bl, and_true_left(Optimizer.same(al, bl), Optimizer.same(ar, br), e)) : {Model.And{al, ar} == Model.And{_, br} : Model.Expr}
      %same_sound(ar, br, and_true_right(Optimizer.same(al, bl), Optimizer.same(ar, br), e)) : {Model.And{al, ar} == Model.And{al, _} : Model.Expr}
      {==}
    case Model.Or{al, ar} Model.Or{bl, br}:
      %same_sound(al, bl, and_true_left(Optimizer.same(al, bl), Optimizer.same(ar, br), e)) : {Model.Or{al, ar} == Model.Or{_, br} : Model.Expr}
      %same_sound(ar, br, and_true_right(Optimizer.same(al, bl), Optimizer.same(ar, br), e)) : {Model.Or{al, ar} == Model.Or{al, _} : Model.Expr}
      {==}
    case Model.Lit{a} Model.Var{b}:
      absurd({Model.Lit{a} == Model.Var{b} : Model.Expr}, bool_clash(e))
    case Model.Lit{a} Model.Not{b}:
      absurd({Model.Lit{a} == Model.Not{b} : Model.Expr}, bool_clash(e))
    case Model.Lit{a} Model.And{bl, br}:
      absurd({Model.Lit{a} == Model.And{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Lit{a} Model.Or{bl, br}:
      absurd({Model.Lit{a} == Model.Or{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Var{a} Model.Lit{b}:
      absurd({Model.Var{a} == Model.Lit{b} : Model.Expr}, bool_clash(e))
    case Model.Var{a} Model.Not{b}:
      absurd({Model.Var{a} == Model.Not{b} : Model.Expr}, bool_clash(e))
    case Model.Var{a} Model.And{bl, br}:
      absurd({Model.Var{a} == Model.And{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Var{a} Model.Or{bl, br}:
      absurd({Model.Var{a} == Model.Or{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Not{a} Model.Lit{b}:
      absurd({Model.Not{a} == Model.Lit{b} : Model.Expr}, bool_clash(e))
    case Model.Not{a} Model.Var{b}:
      absurd({Model.Not{a} == Model.Var{b} : Model.Expr}, bool_clash(e))
    case Model.Not{a} Model.And{bl, br}:
      absurd({Model.Not{a} == Model.And{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Not{a} Model.Or{bl, br}:
      absurd({Model.Not{a} == Model.Or{bl, br} : Model.Expr}, bool_clash(e))
    case Model.And{al, ar} Model.Lit{b}:
      absurd({Model.And{al, ar} == Model.Lit{b} : Model.Expr}, bool_clash(e))
    case Model.And{al, ar} Model.Var{b}:
      absurd({Model.And{al, ar} == Model.Var{b} : Model.Expr}, bool_clash(e))
    case Model.And{al, ar} Model.Not{b}:
      absurd({Model.And{al, ar} == Model.Not{b} : Model.Expr}, bool_clash(e))
    case Model.And{al, ar} Model.Or{bl, br}:
      absurd({Model.And{al, ar} == Model.Or{bl, br} : Model.Expr}, bool_clash(e))
    case Model.Or{al, ar} Model.Lit{b}:
      absurd({Model.Or{al, ar} == Model.Lit{b} : Model.Expr}, bool_clash(e))
    case Model.Or{al, ar} Model.Var{b}:
      absurd({Model.Or{al, ar} == Model.Var{b} : Model.Expr}, bool_clash(e))
    case Model.Or{al, ar} Model.Not{b}:
      absurd({Model.Or{al, ar} == Model.Not{b} : Model.Expr}, bool_clash(e))
    case Model.Or{al, ar} Model.And{bl, br}:
      absurd({Model.Or{al, ar} == Model.And{bl, br} : Model.Expr}, bool_clash(e))

def is_lit(expr: Model.Expr) -> Bool:
  match expr:
    case Model.Lit{value}:
      True{}
    case other:
      False{}

# What both_right and either_right do once right is known not to be a literal.
def and_form(+left: Model.Expr, +right: Model.Expr, complement: Bool, absorbed: Bool) -> Model.Expr:
  Bool.pick(Model.Expr, complement, Model.Lit{False{}}, Bool.pick(Model.Expr, absorbed, left, Model.And{left, right}))

def or_form(+left: Model.Expr, +right: Model.Expr, complement: Bool, absorbed: Bool) -> Model.Expr:
  Bool.pick(Model.Expr, complement, Model.Lit{True{}}, Bool.pick(Model.Expr, absorbed, left, Model.Or{left, right}))

law both_right_fold:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {is_lit(b) == False{} : Bool}
  {and_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implies(a, b)) == Optimizer.both_right(a, b) : Model.Expr}

def both_right_fold(a, b, e):
  match b:
    case Model.Lit{value}:
      absurd({and_form(a, Model.Lit{value}, Optimizer.same(Optimizer.negate(a), Model.Lit{value}), Optimizer.implies(a, Model.Lit{value})) == Optimizer.both_right(a, Model.Lit{value}) : Model.Expr}, true_clash(e))
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law both_fold:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {is_lit(a) == False{} : Bool}
  {Optimizer.both_right(a, b) == Optimizer.both(a, b) : Model.Expr}

def both_fold(a, b, e):
  match a:
    case Model.Lit{value}:
      absurd({Optimizer.both_right(Model.Lit{value}, b) == Optimizer.both(Model.Lit{value}, b) : Model.Expr}, true_clash(e))
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law either_right_fold:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {is_lit(b) == False{} : Bool}
  {or_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implied(a, b)) == Optimizer.either_right(a, b) : Model.Expr}

def either_right_fold(a, b, e):
  match b:
    case Model.Lit{value}:
      absurd({or_form(a, Model.Lit{value}, Optimizer.same(Optimizer.negate(a), Model.Lit{value}), Optimizer.implied(a, Model.Lit{value})) == Optimizer.either_right(a, Model.Lit{value}) : Model.Expr}, true_clash(e))
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law either_fold:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {is_lit(a) == False{} : Bool}
  {Optimizer.either_right(a, b) == Optimizer.either(a, b) : Model.Expr}

def either_fold(a, b, e):
  match a:
    case Model.Lit{value}:
      absurd({Optimizer.either_right(Model.Lit{value}, b) == Optimizer.either(Model.Lit{value}, b) : Model.Expr}, true_clash(e))
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law is_lit_negate:
  for +x: Model.Expr
  for e: {is_lit(x) == False{} : Bool}
  {is_lit(Optimizer.negate(x)) == False{} : Bool}

def is_lit_negate(x, e):
  match x:
    case Model.Lit{value}:
      absurd({is_lit(Optimizer.negate(Model.Lit{value})) == False{} : Bool}, true_clash(e))
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          {==}
        case Model.Var{name}:
          {==}
        case Model.Not{y}:
          {==}
        case Model.And{l, r}:
          {==}
        case Model.Or{l, r}:
          {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law negate_negate:
  for +x: Model.Expr
  {Optimizer.negate(Optimizer.negate(x)) == x : Model.Expr}

def negate_negate(x):
  match x:
    case Model.Lit{value}:
      %bool_not_not(value) : {Model.Lit{Bool.not(Bool.not(value))} == Model.Lit{_} : Model.Expr}
      {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          %bool_not_not(value) : {Model.Not{Model.Lit{Bool.not(Bool.not(value))}} == Model.Not{Model.Lit{_}} : Model.Expr}
          {==}
        case Model.Var{name}:
          {==}
        case Model.Not{y}:
          %negate_negate(y) : {Model.Not{Model.Not{Optimizer.negate(Optimizer.negate(y))}} == Model.Not{Model.Not{_}} : Model.Expr}
          {==}
        case Model.And{l, r}:
          %negate_negate(l) : {Model.Not{Model.And{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))}} == Model.Not{Model.And{_, r}} : Model.Expr}
          %negate_negate(r) : {Model.Not{Model.And{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))}} == Model.Not{Model.And{Optimizer.negate(Optimizer.negate(l)), _}} : Model.Expr}
          {==}
        case Model.Or{l, r}:
          %negate_negate(l) : {Model.Not{Model.Or{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))}} == Model.Not{Model.Or{_, r}} : Model.Expr}
          %negate_negate(r) : {Model.Not{Model.Or{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))}} == Model.Not{Model.Or{Optimizer.negate(Optimizer.negate(l)), _}} : Model.Expr}
          {==}
    case Model.And{l, r}:
      %negate_negate(l) : {Model.And{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))} == Model.And{_, r} : Model.Expr}
      %negate_negate(r) : {Model.And{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))} == Model.And{Optimizer.negate(Optimizer.negate(l)), _} : Model.Expr}
      {==}
    case Model.Or{l, r}:
      %negate_negate(l) : {Model.Or{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))} == Model.Or{_, r} : Model.Expr}
      %negate_negate(r) : {Model.Or{Optimizer.negate(Optimizer.negate(l)), Optimizer.negate(Optimizer.negate(r))} == Model.Or{Optimizer.negate(Optimizer.negate(l)), _} : Model.Expr}
      {==}

law lit_differs:
  for value: Bool
  {Optimizer.same(Model.Lit{Bool.not(value)}, Model.Lit{value}) == False{} : Bool}

def lit_differs(value):
  match value:
    case False{}:
      {==}
    case True{}:
      {==}

# No expression is its own negation.
law negate_differs:
  for +x: Model.Expr
  {Optimizer.same(Optimizer.negate(x), x) == False{} : Bool}

def negate_differs(x):
  match x:
    case Model.Lit{value}:
      lit_differs(value)
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          lit_differs(value)
        case Model.Var{name}:
          {==}
        case Model.Not{y}:
          negate_differs(y)
        case Model.And{l, r}:
          {==}
        case Model.Or{l, r}:
          {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

def wrap(side: Bool, left: Model.Expr, right: Model.Expr) -> Model.Expr:
  match side:
    case True{}:
      Model.Or{left, right}
    case False{}:
      Model.And{left, right}

# An expression's negation never has that expression as its left operand. And
# and Or trade places at each step down, so the claim covers both in one law.
law negate_not_wrap:
  for +a: Model.Expr
  for side: Bool
  for +b: Model.Expr
  {Optimizer.same(Optimizer.negate(a), wrap(side, a, b)) == False{} : Bool}

def negate_not_wrap(a, side, b):
  match a:
    case Model.Lit{value}:
      match side:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      match side:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          match side:
            case True{}:
              {==}
            case False{}:
              {==}
        case Model.Var{name}:
          match side:
            case True{}:
              {==}
            case False{}:
              {==}
        case Model.Not{y}:
          match side:
            case True{}:
              {==}
            case False{}:
              {==}
        case Model.And{l, r}:
          match side:
            case True{}:
              {==}
            case False{}:
              {==}
        case Model.Or{l, r}:
          match side:
            case True{}:
              {==}
            case False{}:
              {==}
    case Model.And{p, q}:
      match side:
        case True{}:
          and_false(Optimizer.same(Optimizer.negate(p), Model.And{p, q}), Optimizer.same(Optimizer.negate(q), b), negate_not_wrap(p, False{}, q))
        case False{}:
          {==}
    case Model.Or{p, q}:
      match side:
        case True{}:
          {==}
        case False{}:
          and_false(Optimizer.same(Optimizer.negate(p), Model.Or{p, q}), Optimizer.same(Optimizer.negate(q), b), negate_not_wrap(p, True{}, q))

law same_of_equal:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {a == b : Model.Expr}
  {Optimizer.same(a, b) == True{} : Bool}

def same_of_equal(a, b, e):
  %e : {Optimizer.same(a, _) == True{} : Bool}
  same_refl(a)

law negate_cancel:
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {Optimizer.negate(a) == Optimizer.negate(b) : Model.Expr}
  {a == b : Model.Expr}

def negate_cancel(a, b, e):
  %negate_negate(b) : {a == _ : Model.Expr}
  %negate_negate(a) : {_ == Optimizer.negate(Optimizer.negate(b)) : Model.Expr}
  %e : {Optimizer.negate(Optimizer.negate(a)) == Optimizer.negate(_) : Model.Expr}
  {==}

law same_negate:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.same(a, b) == Optimizer.same(Optimizer.negate(a), Optimizer.negate(b)) : Bool}

def same_negate(a, b):
  bool_ext(
    Optimizer.same(a, b),
    Optimizer.same(Optimizer.negate(a), Optimizer.negate(b)),
    e => same_of_equal(Optimizer.negate(a), Optimizer.negate(b), Equal.cong(Model.Expr, Model.Expr, Optimizer.negate, a, b, same_sound(a, b, e))),
    e => same_of_equal(a, b, negate_cancel(a, b, same_sound(Optimizer.negate(a), Optimizer.negate(b), e))))

law implies_dual:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.implies(a, b) == Optimizer.implied(Optimizer.negate(a), Optimizer.negate(b)) : Bool}

def implies_dual(a, b):
  match b:
    case Model.Lit{value}:
      same_negate(a, Model.Lit{value})
    case Model.Var{name}:
      same_negate(a, Model.Var{name})
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          same_negate(a, Model.Not{Model.Lit{value}})
        case Model.Var{name}:
          same_negate(a, Model.Not{Model.Var{name}})
        case Model.Not{y}:
          same_negate(a, Model.Not{Model.Not{y}})
        case Model.And{l, r}:
          same_negate(a, Model.Not{Model.And{l, r}})
        case Model.Or{l, r}:
          same_negate(a, Model.Not{Model.Or{l, r}})
    case Model.And{l, r}:
      same_negate(a, Model.And{l, r})
    case Model.Or{l, r}:
      %same_negate(a, Model.Or{l, r}) : {Bool.or(Optimizer.same(a, Model.Or{l, r}), Optimizer.same(a, l)) == Bool.or(_, Optimizer.same(Optimizer.negate(a), Optimizer.negate(l))) : Bool}
      %same_negate(a, l) : {Bool.or(Optimizer.same(a, Model.Or{l, r}), Optimizer.same(a, l)) == Bool.or(Optimizer.same(a, Model.Or{l, r}), _) : Bool}
      {==}

law implied_dual:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.implied(a, b) == Optimizer.implies(Optimizer.negate(a), Optimizer.negate(b)) : Bool}

def implied_dual(a, b):
  match b:
    case Model.Lit{value}:
      same_negate(a, Model.Lit{value})
    case Model.Var{name}:
      same_negate(a, Model.Var{name})
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          same_negate(a, Model.Not{Model.Lit{value}})
        case Model.Var{name}:
          same_negate(a, Model.Not{Model.Var{name}})
        case Model.Not{y}:
          same_negate(a, Model.Not{Model.Not{y}})
        case Model.And{l, r}:
          same_negate(a, Model.Not{Model.And{l, r}})
        case Model.Or{l, r}:
          same_negate(a, Model.Not{Model.Or{l, r}})
    case Model.Or{l, r}:
      same_negate(a, Model.Or{l, r})
    case Model.And{l, r}:
      %same_negate(a, Model.And{l, r}) : {Bool.or(Optimizer.same(a, Model.And{l, r}), Optimizer.same(a, l)) == Bool.or(_, Optimizer.same(Optimizer.negate(a), Optimizer.negate(l))) : Bool}
      %same_negate(a, l) : {Bool.or(Optimizer.same(a, Model.And{l, r}), Optimizer.same(a, l)) == Bool.or(Optimizer.same(a, Model.And{l, r}), _) : Bool}
      {==}

law negate_and_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for c: Bool
  for d: Bool
  {Optimizer.negate(and_form(a, b, c, d)) == or_form(Optimizer.negate(a), Optimizer.negate(b), c, d) : Model.Expr}

def negate_and_form(a, b, c, d):
  match c:
    case True{}:
      {==}
    case False{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

law negate_or_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for c: Bool
  for d: Bool
  {Optimizer.negate(or_form(a, b, c, d)) == and_form(Optimizer.negate(a), Optimizer.negate(b), c, d) : Model.Expr}

def negate_or_form(a, b, c, d):
  match c:
    case True{}:
      {==}
    case False{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

law negate_both_other:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {is_lit(b) == False{} : Bool}
  {Optimizer.negate(Optimizer.both_right(a, b)) == Optimizer.either_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_both_other(a, b, e):
  %either_right_fold(Optimizer.negate(a), Optimizer.negate(b), is_lit_negate(b, e)) : {Optimizer.negate(Optimizer.both_right(a, b)) == _ : Model.Expr}
  %both_right_fold(a, b, e) : {Optimizer.negate(_) == or_form(Optimizer.negate(a), Optimizer.negate(b), Optimizer.same(Optimizer.negate(Optimizer.negate(a)), Optimizer.negate(b)), Optimizer.implied(Optimizer.negate(a), Optimizer.negate(b))) : Model.Expr}
  %same_negate(Optimizer.negate(a), b) : {Optimizer.negate(and_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implies(a, b))) == or_form(Optimizer.negate(a), Optimizer.negate(b), _, Optimizer.implied(Optimizer.negate(a), Optimizer.negate(b))) : Model.Expr}
  %implies_dual(a, b) : {Optimizer.negate(and_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implies(a, b))) == or_form(Optimizer.negate(a), Optimizer.negate(b), Optimizer.same(Optimizer.negate(a), b), _) : Model.Expr}
  negate_and_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implies(a, b))

law negate_both_right:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.negate(Optimizer.both_right(a, b)) == Optimizer.either_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_both_right(a, b):
  match b:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      negate_both_other(a, Model.Var{name}, {==})
    case Model.Not{inner}:
      negate_both_other(a, Model.Not{inner}, {==})
    case Model.And{l, r}:
      negate_both_other(a, Model.And{l, r}, {==})
    case Model.Or{l, r}:
      negate_both_other(a, Model.Or{l, r}, {==})

law negate_both_nonlit:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {is_lit(a) == False{} : Bool}
  {Optimizer.negate(Optimizer.both(a, b)) == Optimizer.either(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_both_nonlit(a, b, e):
  %either_fold(Optimizer.negate(a), Optimizer.negate(b), is_lit_negate(a, e)) : {Optimizer.negate(Optimizer.both(a, b)) == _ : Model.Expr}
  %both_fold(a, b, e) : {Optimizer.negate(_) == Optimizer.either_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}
  negate_both_right(a, b)

law negate_both:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.negate(Optimizer.both(a, b)) == Optimizer.either(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_both(a, b):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      negate_both_nonlit(Model.Var{name}, b, {==})
    case Model.Not{inner}:
      negate_both_nonlit(Model.Not{inner}, b, {==})
    case Model.And{l, r}:
      negate_both_nonlit(Model.And{l, r}, b, {==})
    case Model.Or{l, r}:
      negate_both_nonlit(Model.Or{l, r}, b, {==})

law negate_either_other:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {is_lit(b) == False{} : Bool}
  {Optimizer.negate(Optimizer.either_right(a, b)) == Optimizer.both_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_either_other(a, b, e):
  %both_right_fold(Optimizer.negate(a), Optimizer.negate(b), is_lit_negate(b, e)) : {Optimizer.negate(Optimizer.either_right(a, b)) == _ : Model.Expr}
  %either_right_fold(a, b, e) : {Optimizer.negate(_) == and_form(Optimizer.negate(a), Optimizer.negate(b), Optimizer.same(Optimizer.negate(Optimizer.negate(a)), Optimizer.negate(b)), Optimizer.implies(Optimizer.negate(a), Optimizer.negate(b))) : Model.Expr}
  %same_negate(Optimizer.negate(a), b) : {Optimizer.negate(or_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implied(a, b))) == and_form(Optimizer.negate(a), Optimizer.negate(b), _, Optimizer.implies(Optimizer.negate(a), Optimizer.negate(b))) : Model.Expr}
  %implied_dual(a, b) : {Optimizer.negate(or_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implied(a, b))) == and_form(Optimizer.negate(a), Optimizer.negate(b), Optimizer.same(Optimizer.negate(a), b), _) : Model.Expr}
  negate_or_form(a, b, Optimizer.same(Optimizer.negate(a), b), Optimizer.implied(a, b))

law negate_either_right:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.negate(Optimizer.either_right(a, b)) == Optimizer.both_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_either_right(a, b):
  match b:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      negate_either_other(a, Model.Var{name}, {==})
    case Model.Not{inner}:
      negate_either_other(a, Model.Not{inner}, {==})
    case Model.And{l, r}:
      negate_either_other(a, Model.And{l, r}, {==})
    case Model.Or{l, r}:
      negate_either_other(a, Model.Or{l, r}, {==})

law negate_either_nonlit:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {is_lit(a) == False{} : Bool}
  {Optimizer.negate(Optimizer.either(a, b)) == Optimizer.both(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_either_nonlit(a, b, e):
  %both_fold(Optimizer.negate(a), Optimizer.negate(b), is_lit_negate(a, e)) : {Optimizer.negate(Optimizer.either(a, b)) == _ : Model.Expr}
  %either_fold(a, b, e) : {Optimizer.negate(_) == Optimizer.both_right(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}
  negate_either_right(a, b)

law negate_either:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.negate(Optimizer.either(a, b)) == Optimizer.both(Optimizer.negate(a), Optimizer.negate(b)) : Model.Expr}

def negate_either(a, b):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      negate_either_nonlit(Model.Var{name}, b, {==})
    case Model.Not{inner}:
      negate_either_nonlit(Model.Not{inner}, b, {==})
    case Model.And{l, r}:
      negate_either_nonlit(Model.And{l, r}, b, {==})
    case Model.Or{l, r}:
      negate_either_nonlit(Model.Or{l, r}, b, {==})

law both_keeps_left:
  for +a: Model.Expr
  for +b: Model.Expr
  for al: {is_lit(a) == False{} : Bool}
  for bl: {is_lit(b) == False{} : Bool}
  for ce: {Optimizer.same(Optimizer.negate(a), b) == False{} : Bool}
  for de: {Optimizer.implies(a, b) == True{} : Bool}
  {Optimizer.both(a, b) == a : Model.Expr}

def both_keeps_left(a, b, al, bl, ce, de):
  %both_fold(a, b, al) : {_ == a : Model.Expr}
  %both_right_fold(a, b, bl) : {_ == a : Model.Expr}
  %Equal.sym(Bool, Optimizer.same(Optimizer.negate(a), b), False{}, ce) : {and_form(a, b, _, Optimizer.implies(a, b)) == a : Model.Expr}
  %Equal.sym(Bool, Optimizer.implies(a, b), True{}, de) : {and_form(a, b, False{}, _) == a : Model.Expr}
  {==}

law both_complement_nonlit:
  for +a: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.both(a, Optimizer.negate(a)) == Model.Lit{False{}} : Model.Expr}

def both_complement_nonlit(a, al):
  %both_fold(a, Optimizer.negate(a), al) : {_ == Model.Lit{False{}} : Model.Expr}
  %both_right_fold(a, Optimizer.negate(a), is_lit_negate(a, al)) : {_ == Model.Lit{False{}} : Model.Expr}
  %Equal.sym(Bool, Optimizer.same(Optimizer.negate(a), Optimizer.negate(a)), True{}, same_refl(Optimizer.negate(a))) : {and_form(a, Optimizer.negate(a), _, Optimizer.implies(a, Optimizer.negate(a))) == Model.Lit{False{}} : Model.Expr}
  {==}

law both_complement:
  for +a: Model.Expr
  {Optimizer.both(a, Optimizer.negate(a)) == Model.Lit{False{}} : Model.Expr}

def both_complement(a):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      both_complement_nonlit(Model.Var{name}, {==})
    case Model.Not{inner}:
      both_complement_nonlit(Model.Not{inner}, {==})
    case Model.And{l, r}:
      both_complement_nonlit(Model.And{l, r}, {==})
    case Model.Or{l, r}:
      both_complement_nonlit(Model.Or{l, r}, {==})

law implies_self:
  for +a: Model.Expr
  {Optimizer.implies(a, a) == True{} : Bool}

def implies_self(a):
  match a:
    case Model.Lit{value}:
      same_refl(Model.Lit{value})
    case Model.Var{name}:
      same_refl(Model.Var{name})
    case Model.Not{inner}:
      same_refl(Model.Not{inner})
    case Model.And{l, r}:
      same_refl(Model.And{l, r})
    case Model.Or{l, r}:
      or_true_left(Optimizer.same(Model.Or{l, r}, Model.Or{l, r}), Optimizer.same(Model.Or{l, r}, l), same_refl(Model.Or{l, r}))

law both_self:
  for +a: Model.Expr
  {Optimizer.both(a, a) == a : Model.Expr}

def both_self(a):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      both_keeps_left(Model.Var{name}, Model.Var{name}, {==}, {==}, negate_differs(Model.Var{name}), implies_self(Model.Var{name}))
    case Model.Not{inner}:
      both_keeps_left(Model.Not{inner}, Model.Not{inner}, {==}, {==}, negate_differs(Model.Not{inner}), implies_self(Model.Not{inner}))
    case Model.And{l, r}:
      both_keeps_left(Model.And{l, r}, Model.And{l, r}, {==}, {==}, negate_differs(Model.And{l, r}), implies_self(Model.And{l, r}))
    case Model.Or{l, r}:
      both_keeps_left(Model.Or{l, r}, Model.Or{l, r}, {==}, {==}, negate_differs(Model.Or{l, r}), implies_self(Model.Or{l, r}))

law either_keeps_left:
  for +a: Model.Expr
  for +b: Model.Expr
  for al: {is_lit(a) == False{} : Bool}
  for bl: {is_lit(b) == False{} : Bool}
  for ce: {Optimizer.same(Optimizer.negate(a), b) == False{} : Bool}
  for de: {Optimizer.implied(a, b) == True{} : Bool}
  {Optimizer.either(a, b) == a : Model.Expr}

def either_keeps_left(a, b, al, bl, ce, de):
  %either_fold(a, b, al) : {_ == a : Model.Expr}
  %either_right_fold(a, b, bl) : {_ == a : Model.Expr}
  %Equal.sym(Bool, Optimizer.same(Optimizer.negate(a), b), False{}, ce) : {or_form(a, b, _, Optimizer.implied(a, b)) == a : Model.Expr}
  %Equal.sym(Bool, Optimizer.implied(a, b), True{}, de) : {or_form(a, b, False{}, _) == a : Model.Expr}
  {==}

law either_complement_nonlit:
  for +a: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.either(a, Optimizer.negate(a)) == Model.Lit{True{}} : Model.Expr}

def either_complement_nonlit(a, al):
  %either_fold(a, Optimizer.negate(a), al) : {_ == Model.Lit{True{}} : Model.Expr}
  %either_right_fold(a, Optimizer.negate(a), is_lit_negate(a, al)) : {_ == Model.Lit{True{}} : Model.Expr}
  %Equal.sym(Bool, Optimizer.same(Optimizer.negate(a), Optimizer.negate(a)), True{}, same_refl(Optimizer.negate(a))) : {or_form(a, Optimizer.negate(a), _, Optimizer.implied(a, Optimizer.negate(a))) == Model.Lit{True{}} : Model.Expr}
  {==}

law either_complement:
  for +a: Model.Expr
  {Optimizer.either(a, Optimizer.negate(a)) == Model.Lit{True{}} : Model.Expr}

def either_complement(a):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      either_complement_nonlit(Model.Var{name}, {==})
    case Model.Not{inner}:
      either_complement_nonlit(Model.Not{inner}, {==})
    case Model.And{l, r}:
      either_complement_nonlit(Model.And{l, r}, {==})
    case Model.Or{l, r}:
      either_complement_nonlit(Model.Or{l, r}, {==})

law implied_self:
  for +a: Model.Expr
  {Optimizer.implied(a, a) == True{} : Bool}

def implied_self(a):
  match a:
    case Model.Lit{value}:
      same_refl(Model.Lit{value})
    case Model.Var{name}:
      same_refl(Model.Var{name})
    case Model.Not{inner}:
      same_refl(Model.Not{inner})
    case Model.And{l, r}:
      or_true_left(Optimizer.same(Model.And{l, r}, Model.And{l, r}), Optimizer.same(Model.And{l, r}, l), same_refl(Model.And{l, r}))
    case Model.Or{l, r}:
      same_refl(Model.Or{l, r})

law either_self:
  for +a: Model.Expr
  {Optimizer.either(a, a) == a : Model.Expr}

def either_self(a):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      either_keeps_left(Model.Var{name}, Model.Var{name}, {==}, {==}, negate_differs(Model.Var{name}), implied_self(Model.Var{name}))
    case Model.Not{inner}:
      either_keeps_left(Model.Not{inner}, Model.Not{inner}, {==}, {==}, negate_differs(Model.Not{inner}), implied_self(Model.Not{inner}))
    case Model.And{l, r}:
      either_keeps_left(Model.And{l, r}, Model.And{l, r}, {==}, {==}, negate_differs(Model.And{l, r}), implied_self(Model.And{l, r}))
    case Model.Or{l, r}:
      either_keeps_left(Model.Or{l, r}, Model.Or{l, r}, {==}, {==}, negate_differs(Model.Or{l, r}), implied_self(Model.Or{l, r}))

law either_and_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for c: Bool
  for d: Bool
  for al: {is_lit(a) == False{} : Bool}
  {Optimizer.either(a, and_form(a, b, c, d)) == a : Model.Expr}

def either_and_form(a, b, c, d, al):
  match c:
    case True{}:
      either_false_right(a)
    case False{}:
      match d:
        case True{}:
          either_self(a)
        case False{}:
          either_keeps_left(a, Model.And{a, b}, al, {==}, negate_not_wrap(a, False{}, b), or_true_right(Optimizer.same(a, Model.And{a, b}), Optimizer.same(a, a), same_refl(a)))

law either_absorbs_right:
  for +a: Model.Expr
  for +b: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.either(a, Optimizer.both_right(a, b)) == a : Model.Expr}

def either_absorbs_right(a, b, al):
  match b:
    case Model.Lit{value}:
      match value:
        case True{}:
          either_self(a)
        case False{}:
          either_false_right(a)
    case Model.Var{name}:
      either_and_form(a, Model.Var{name}, Optimizer.same(Optimizer.negate(a), Model.Var{name}), Optimizer.implies(a, Model.Var{name}), al)
    case Model.Not{inner}:
      either_and_form(a, Model.Not{inner}, Optimizer.same(Optimizer.negate(a), Model.Not{inner}), Optimizer.implies(a, Model.Not{inner}), al)
    case Model.And{l, r}:
      either_and_form(a, Model.And{l, r}, Optimizer.same(Optimizer.negate(a), Model.And{l, r}), Optimizer.implies(a, Model.And{l, r}), al)
    case Model.Or{l, r}:
      either_and_form(a, Model.Or{l, r}, Optimizer.same(Optimizer.negate(a), Model.Or{l, r}), Optimizer.implies(a, Model.Or{l, r}), al)

law either_absorbs_nonlit:
  for +a: Model.Expr
  for +b: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.either(a, Optimizer.both(a, b)) == a : Model.Expr}

def either_absorbs_nonlit(a, b, al):
  %both_fold(a, b, al) : {Optimizer.either(a, _) == a : Model.Expr}
  either_absorbs_right(a, b, al)

law either_absorbs:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.either(a, Optimizer.both(a, b)) == a : Model.Expr}

def either_absorbs(a, b):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      either_absorbs_nonlit(Model.Var{name}, b, {==})
    case Model.Not{inner}:
      either_absorbs_nonlit(Model.Not{inner}, b, {==})
    case Model.And{l, r}:
      either_absorbs_nonlit(Model.And{l, r}, b, {==})
    case Model.Or{l, r}:
      either_absorbs_nonlit(Model.Or{l, r}, b, {==})

law both_or_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for c: Bool
  for d: Bool
  for al: {is_lit(a) == False{} : Bool}
  {Optimizer.both(a, or_form(a, b, c, d)) == a : Model.Expr}

def both_or_form(a, b, c, d, al):
  match c:
    case True{}:
      both_true_right(a)
    case False{}:
      match d:
        case True{}:
          both_self(a)
        case False{}:
          both_keeps_left(a, Model.Or{a, b}, al, {==}, negate_not_wrap(a, True{}, b), or_true_right(Optimizer.same(a, Model.Or{a, b}), Optimizer.same(a, a), same_refl(a)))

law both_absorbs_right:
  for +a: Model.Expr
  for +b: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.both(a, Optimizer.either_right(a, b)) == a : Model.Expr}

def both_absorbs_right(a, b, al):
  match b:
    case Model.Lit{value}:
      match value:
        case True{}:
          both_true_right(a)
        case False{}:
          both_self(a)
    case Model.Var{name}:
      both_or_form(a, Model.Var{name}, Optimizer.same(Optimizer.negate(a), Model.Var{name}), Optimizer.implied(a, Model.Var{name}), al)
    case Model.Not{inner}:
      both_or_form(a, Model.Not{inner}, Optimizer.same(Optimizer.negate(a), Model.Not{inner}), Optimizer.implied(a, Model.Not{inner}), al)
    case Model.And{l, r}:
      both_or_form(a, Model.And{l, r}, Optimizer.same(Optimizer.negate(a), Model.And{l, r}), Optimizer.implied(a, Model.And{l, r}), al)
    case Model.Or{l, r}:
      both_or_form(a, Model.Or{l, r}, Optimizer.same(Optimizer.negate(a), Model.Or{l, r}), Optimizer.implied(a, Model.Or{l, r}), al)

law both_absorbs_nonlit:
  for +a: Model.Expr
  for +b: Model.Expr
  for +al: {is_lit(a) == False{} : Bool}
  {Optimizer.both(a, Optimizer.either(a, b)) == a : Model.Expr}

def both_absorbs_nonlit(a, b, al):
  %either_fold(a, b, al) : {Optimizer.both(a, _) == a : Model.Expr}
  both_absorbs_right(a, b, al)

law both_absorbs:
  for +a: Model.Expr
  for +b: Model.Expr
  {Optimizer.both(a, Optimizer.either(a, b)) == a : Model.Expr}

def both_absorbs(a, b):
  match a:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      both_absorbs_nonlit(Model.Var{name}, b, {==})
    case Model.Not{inner}:
      both_absorbs_nonlit(Model.Not{inner}, b, {==})
    case Model.And{l, r}:
      both_absorbs_nonlit(Model.And{l, r}, b, {==})
    case Model.Or{l, r}:
      both_absorbs_nonlit(Model.Or{l, r}, b, {==})

law eval_negate_and:
  for +l: Model.Expr
  for +r: Model.Expr
  for +env: Model.Env
  for el: {Model.eval(Optimizer.negate(l), env) == Bool.not(Model.eval(l, env)) : Bool}
  for er: {Model.eval(Optimizer.negate(r), env) == Bool.not(Model.eval(r, env)) : Bool}
  {Bool.or(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.not(Bool.and(Model.eval(l, env), Model.eval(r, env))) : Bool}

def eval_negate_and(l, r, env, el, er):
  %bool_or_not(Model.eval(l, env), Model.eval(r, env)) : {Bool.or(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == _ : Bool}
  %el : {Bool.or(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.or(_, Bool.not(Model.eval(r, env))) : Bool}
  %er : {Bool.or(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.or(Model.eval(Optimizer.negate(l), env), _) : Bool}
  {==}

law eval_negate_or:
  for +l: Model.Expr
  for +r: Model.Expr
  for +env: Model.Env
  for el: {Model.eval(Optimizer.negate(l), env) == Bool.not(Model.eval(l, env)) : Bool}
  for er: {Model.eval(Optimizer.negate(r), env) == Bool.not(Model.eval(r, env)) : Bool}
  {Bool.and(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.not(Bool.or(Model.eval(l, env), Model.eval(r, env))) : Bool}

def eval_negate_or(l, r, env, el, er):
  %bool_and_not(Model.eval(l, env), Model.eval(r, env)) : {Bool.and(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == _ : Bool}
  %el : {Bool.and(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.and(_, Bool.not(Model.eval(r, env))) : Bool}
  %er : {Bool.and(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env)) == Bool.and(Model.eval(Optimizer.negate(l), env), _) : Bool}
  {==}

law eval_negate:
  for +expr: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.negate(expr), env) == Bool.not(Model.eval(expr, env)) : Bool}

def eval_negate(expr, env):
  match expr:
    case Model.Lit{value}:
      {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      match inner:
        case Model.Lit{value}:
          {==}
        case Model.Var{name}:
          Equal.sym(Bool, Bool.not(Bool.not(Model.eval(Model.Var{name}, env))), Model.eval(Model.Var{name}, env), bool_not_not(Model.eval(Model.Var{name}, env)))
        case Model.Not{y}:
          %eval_negate(y, env) : {Bool.not(Bool.not(Model.eval(Optimizer.negate(y), env))) == Bool.not(Bool.not(_)) : Bool}
          {==}
        case Model.And{l, r}:
          %eval_negate_and(l, r, env, eval_negate(l, env), eval_negate(r, env)) : {Bool.not(Bool.or(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env))) == Bool.not(_) : Bool}
          {==}
        case Model.Or{l, r}:
          %eval_negate_or(l, r, env, eval_negate(l, env), eval_negate(r, env)) : {Bool.not(Bool.and(Model.eval(Optimizer.negate(l), env), Model.eval(Optimizer.negate(r), env))) == Bool.not(_) : Bool}
          {==}
    case Model.And{l, r}:
      eval_negate_and(l, r, env, eval_negate(l, env), eval_negate(r, env))
    case Model.Or{l, r}:
      eval_negate_or(l, r, env, eval_negate(l, env), eval_negate(r, env))

law eval_and_same:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for e: {Optimizer.same(a, b) == True{} : Bool}
  {Bool.and(Model.eval(a, env), Model.eval(b, env)) == Model.eval(a, env) : Bool}

def eval_and_same(a, b, env, e):
  %same_sound(a, b, e) : {Bool.and(Model.eval(a, env), Model.eval(_, env)) == Model.eval(a, env) : Bool}
  bool_and_self(Model.eval(a, env))

law eval_and_wrapped:
  for +a: Model.Expr
  for +x: Model.Expr
  for +y: Model.Expr
  for +env: Model.Env
  for p: Bool
  for q: Bool
  for pe: {Optimizer.same(a, Model.Or{x, y}) == p : Bool}
  for qe: {Optimizer.same(a, x) == q : Bool}
  for e: {Bool.or(p, q) == True{} : Bool}
  {Bool.and(Model.eval(a, env), Model.eval(Model.Or{x, y}, env)) == Model.eval(a, env) : Bool}

def eval_and_wrapped(a, x, y, env, p, q, pe, qe, e):
  match p:
    case True{}:
      eval_and_same(a, Model.Or{x, y}, env, pe)
    case False{}:
      %same_sound(a, x, Equal.trans(Bool, Optimizer.same(a, x), q, True{}, qe, e)) : {Bool.and(Model.eval(a, env), Bool.or(Model.eval(_, env), Model.eval(y, env))) == Model.eval(a, env) : Bool}
      bool_and_or(Model.eval(a, env), Model.eval(y, env))

law eval_implies:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for e: {Optimizer.implies(a, b) == True{} : Bool}
  {Bool.and(Model.eval(a, env), Model.eval(b, env)) == Model.eval(a, env) : Bool}

def eval_implies(a, b, env, e):
  match b:
    case Model.Lit{value}:
      eval_and_same(a, Model.Lit{value}, env, e)
    case Model.Var{name}:
      eval_and_same(a, Model.Var{name}, env, e)
    case Model.Not{inner}:
      eval_and_same(a, Model.Not{inner}, env, e)
    case Model.And{l, r}:
      eval_and_same(a, Model.And{l, r}, env, e)
    case Model.Or{l, r}:
      eval_and_wrapped(a, l, r, env, Optimizer.same(a, Model.Or{l, r}), Optimizer.same(a, l), {==}, {==}, e)

law eval_or_same:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for e: {Optimizer.same(a, b) == True{} : Bool}
  {Bool.or(Model.eval(a, env), Model.eval(b, env)) == Model.eval(a, env) : Bool}

def eval_or_same(a, b, env, e):
  %same_sound(a, b, e) : {Bool.or(Model.eval(a, env), Model.eval(_, env)) == Model.eval(a, env) : Bool}
  bool_or_self(Model.eval(a, env))

law eval_or_wrapped:
  for +a: Model.Expr
  for +x: Model.Expr
  for +y: Model.Expr
  for +env: Model.Env
  for p: Bool
  for q: Bool
  for pe: {Optimizer.same(a, Model.And{x, y}) == p : Bool}
  for qe: {Optimizer.same(a, x) == q : Bool}
  for e: {Bool.or(p, q) == True{} : Bool}
  {Bool.or(Model.eval(a, env), Model.eval(Model.And{x, y}, env)) == Model.eval(a, env) : Bool}

def eval_or_wrapped(a, x, y, env, p, q, pe, qe, e):
  match p:
    case True{}:
      eval_or_same(a, Model.And{x, y}, env, pe)
    case False{}:
      %same_sound(a, x, Equal.trans(Bool, Optimizer.same(a, x), q, True{}, qe, e)) : {Bool.or(Model.eval(a, env), Bool.and(Model.eval(_, env), Model.eval(y, env))) == Model.eval(a, env) : Bool}
      bool_or_and(Model.eval(a, env), Model.eval(y, env))

law eval_implied:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for e: {Optimizer.implied(a, b) == True{} : Bool}
  {Bool.or(Model.eval(a, env), Model.eval(b, env)) == Model.eval(a, env) : Bool}

def eval_implied(a, b, env, e):
  match b:
    case Model.Lit{value}:
      eval_or_same(a, Model.Lit{value}, env, e)
    case Model.Var{name}:
      eval_or_same(a, Model.Var{name}, env, e)
    case Model.Not{inner}:
      eval_or_same(a, Model.Not{inner}, env, e)
    case Model.And{l, r}:
      eval_or_wrapped(a, l, r, env, Optimizer.same(a, Model.And{l, r}), Optimizer.same(a, l), {==}, {==}, e)
    case Model.Or{l, r}:
      eval_or_same(a, Model.Or{l, r}, env, e)

law eval_and_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for c: Bool
  for d: Bool
  for ce: {Optimizer.same(Optimizer.negate(a), b) == c : Bool}
  for de: {Optimizer.implies(a, b) == d : Bool}
  {Model.eval(and_form(a, b, c, d), env) == Bool.and(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_and_form(a, b, env, c, d, ce, de):
  match c:
    case True{}:
      %same_sound(Optimizer.negate(a), b, ce) : {False{} == Bool.and(Model.eval(a, env), Model.eval(_, env)) : Bool}
      %Equal.sym(Bool, Model.eval(Optimizer.negate(a), env), Bool.not(Model.eval(a, env)), eval_negate(a, env)) : {False{} == Bool.and(Model.eval(a, env), _) : Bool}
      Equal.sym(Bool, Bool.and(Model.eval(a, env), Bool.not(Model.eval(a, env))), False{}, bool_and_not_self(Model.eval(a, env)))
    case False{}:
      match d:
        case True{}:
          Equal.sym(Bool, Bool.and(Model.eval(a, env), Model.eval(b, env)), Model.eval(a, env), eval_implies(a, b, env, de))
        case False{}:
          {==}

law eval_both_right:
  for +left: Model.Expr
  for +right: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.both_right(left, right), env) == Bool.and(Model.eval(left, env), Model.eval(right, env)) : Bool}

def eval_both_right(left, right, env):
  match right:
    case Model.Lit{value}:
      match value:

        case True{}:
          Equal.sym(Bool, Bool.and(Model.eval(left, env), True{}), Model.eval(left, env), bool_and_true(Model.eval(left, env)))
        case False{}:
          Equal.sym(Bool, Bool.and(Model.eval(left, env), False{}), False{}, bool_and_false(Model.eval(left, env)))
    case Model.Var{name}:
      eval_and_form(left, Model.Var{name}, env, Optimizer.same(Optimizer.negate(left), Model.Var{name}), Optimizer.implies(left, Model.Var{name}), {==}, {==})
    case Model.Not{inner}:
      eval_and_form(left, Model.Not{inner}, env, Optimizer.same(Optimizer.negate(left), Model.Not{inner}), Optimizer.implies(left, Model.Not{inner}), {==}, {==})
    case Model.And{l, r}:
      eval_and_form(left, Model.And{l, r}, env, Optimizer.same(Optimizer.negate(left), Model.And{l, r}), Optimizer.implies(left, Model.And{l, r}), {==}, {==})
    case Model.Or{l, r}:
      eval_and_form(left, Model.Or{l, r}, env, Optimizer.same(Optimizer.negate(left), Model.Or{l, r}), Optimizer.implies(left, Model.Or{l, r}), {==}, {==})

law eval_both:
  for +left: Model.Expr
  for +right: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.both(left, right), env) == Bool.and(Model.eval(left, env), Model.eval(right, env)) : Bool}

def eval_both(left, right, env):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      eval_both_right(Model.Var{name}, right, env)
    case Model.Not{inner}:
      eval_both_right(Model.Not{inner}, right, env)
    case Model.And{l, r}:
      eval_both_right(Model.And{l, r}, right, env)
    case Model.Or{l, r}:
      eval_both_right(Model.Or{l, r}, right, env)

law eval_or_form:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  for c: Bool
  for d: Bool
  for ce: {Optimizer.same(Optimizer.negate(a), b) == c : Bool}
  for de: {Optimizer.implied(a, b) == d : Bool}
  {Model.eval(or_form(a, b, c, d), env) == Bool.or(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_or_form(a, b, env, c, d, ce, de):
  match c:
    case True{}:
      %same_sound(Optimizer.negate(a), b, ce) : {True{} == Bool.or(Model.eval(a, env), Model.eval(_, env)) : Bool}
      %Equal.sym(Bool, Model.eval(Optimizer.negate(a), env), Bool.not(Model.eval(a, env)), eval_negate(a, env)) : {True{} == Bool.or(Model.eval(a, env), _) : Bool}
      Equal.sym(Bool, Bool.or(Model.eval(a, env), Bool.not(Model.eval(a, env))), True{}, bool_or_not_self(Model.eval(a, env)))
    case False{}:
      match d:
        case True{}:
          Equal.sym(Bool, Bool.or(Model.eval(a, env), Model.eval(b, env)), Model.eval(a, env), eval_implied(a, b, env, de))
        case False{}:
          {==}

law eval_either_right:
  for +left: Model.Expr
  for +right: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.either_right(left, right), env) == Bool.or(Model.eval(left, env), Model.eval(right, env)) : Bool}

def eval_either_right(left, right, env):
  match right:
    case Model.Lit{value}:
      match value:

        case True{}:
          Equal.sym(Bool, Bool.or(Model.eval(left, env), True{}), True{}, bool_or_true(Model.eval(left, env)))
        case False{}:
          Equal.sym(Bool, Bool.or(Model.eval(left, env), False{}), Model.eval(left, env), bool_or_false(Model.eval(left, env)))
    case Model.Var{name}:
      eval_or_form(left, Model.Var{name}, env, Optimizer.same(Optimizer.negate(left), Model.Var{name}), Optimizer.implied(left, Model.Var{name}), {==}, {==})
    case Model.Not{inner}:
      eval_or_form(left, Model.Not{inner}, env, Optimizer.same(Optimizer.negate(left), Model.Not{inner}), Optimizer.implied(left, Model.Not{inner}), {==}, {==})
    case Model.And{l, r}:
      eval_or_form(left, Model.And{l, r}, env, Optimizer.same(Optimizer.negate(left), Model.And{l, r}), Optimizer.implied(left, Model.And{l, r}), {==}, {==})
    case Model.Or{l, r}:
      eval_or_form(left, Model.Or{l, r}, env, Optimizer.same(Optimizer.negate(left), Model.Or{l, r}), Optimizer.implied(left, Model.Or{l, r}), {==}, {==})

law eval_either:
  for +left: Model.Expr
  for +right: Model.Expr
  for +env: Model.Env
  {Model.eval(Optimizer.either(left, right), env) == Bool.or(Model.eval(left, env), Model.eval(right, env)) : Bool}

def eval_either(left, right, env):
  match left:
    case Model.Lit{value}:
      match value:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{name}:
      eval_either_right(Model.Var{name}, right, env)
    case Model.Not{inner}:
      eval_either_right(Model.Not{inner}, right, env)
    case Model.And{l, r}:
      eval_either_right(Model.And{l, r}, right, env)
    case Model.Or{l, r}:
      eval_either_right(Model.Or{l, r}, right, env)

def Laws.preserves_meaning(expr, env):
  match expr:
    case Model.Lit{value}:
      {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      %Laws.preserves_meaning(inner, env) : {Model.eval(Optimizer.negate(Optimizer.optimize(inner)), env) == Bool.not(_) : Bool}
      eval_negate(Optimizer.optimize(inner), env)
    case Model.And{left, right}:
      %Laws.preserves_meaning(left, env) : {Model.eval(Optimizer.both(Optimizer.optimize(left), Optimizer.optimize(right)), env) == Bool.and(_, Model.eval(right, env)) : Bool}
      %Laws.preserves_meaning(right, env) : {Model.eval(Optimizer.both(Optimizer.optimize(left), Optimizer.optimize(right)), env) == Bool.and(Model.eval(Optimizer.optimize(left), env), _) : Bool}
      eval_both(Optimizer.optimize(left), Optimizer.optimize(right), env)
    case Model.Or{left, right}:
      %Laws.preserves_meaning(left, env) : {Model.eval(Optimizer.either(Optimizer.optimize(left), Optimizer.optimize(right)), env) == Bool.or(_, Model.eval(right, env)) : Bool}
      %Laws.preserves_meaning(right, env) : {Model.eval(Optimizer.either(Optimizer.optimize(left), Optimizer.optimize(right)), env) == Bool.or(Model.eval(Optimizer.optimize(left), env), _) : Bool}
      eval_either(Optimizer.optimize(left), Optimizer.optimize(right), env)

def Laws.keeps_variables(name):
  {==}

def Laws.keeps_literals(value):
  {==}

def Laws.removes_double_not(expr):
  negate_negate(Optimizer.optimize(expr))

def Laws.folds_not_true():
  {==}

def Laws.folds_not_false():
  {==}

def Laws.simplifies_and_true(expr):
  {==}

def Laws.simplifies_and_false(expr):
  {==}

def Laws.simplifies_or_false(expr):
  {==}

def Laws.simplifies_or_true(expr):
  {==}

def Laws.simplifies_and_true_right(expr):
  both_true_right(Optimizer.optimize(expr))

def Laws.simplifies_and_false_right(expr):
  both_false_right(Optimizer.optimize(expr))

def Laws.simplifies_or_false_right(expr):
  either_false_right(Optimizer.optimize(expr))

def Laws.simplifies_or_true_right(expr):
  either_true_right(Optimizer.optimize(expr))

def Laws.de_morgan_and(left, right):
  negate_both(Optimizer.optimize(left), Optimizer.optimize(right))

def Laws.de_morgan_or(left, right):
  negate_either(Optimizer.optimize(left), Optimizer.optimize(right))

def Laws.removes_contradiction(expr):
  both_complement(Optimizer.optimize(expr))

def Laws.removes_excluded_middle(expr):
  either_complement(Optimizer.optimize(expr))

def Laws.and_idempotent(expr):
  both_self(Optimizer.optimize(expr))

def Laws.or_idempotent(expr):
  either_self(Optimizer.optimize(expr))

def Laws.absorbs_and_in_or(left, right):
  either_absorbs(Optimizer.optimize(left), Optimizer.optimize(right))

def Laws.absorbs_or_in_and(left, right):
  both_absorbs(Optimizer.optimize(left), Optimizer.optimize(right))
