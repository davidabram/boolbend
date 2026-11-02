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

def Le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

def Lt(a: Nat, b: Nat) -> Data:
  Le(1n+a, b)

law le_zero:
  for +n: Nat
  Le(0n, n)

def le_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law le_refl:
  for +n: Nat
  Le(n, n)

def le_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: Le(a, b)
  for bc: Le(b, c)
  Le(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n b c:
      le_zero(c)
    case 1n+p 0n c:
      absurd(Le(1n+p, c), bool_clash(ab))
    case 1n+p 1n+q 0n:
      absurd(Le(1n+p, 0n), bool_clash(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

law le_succ:
  for +n: Nat
  Le(n, 1n+n)

def le_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

law le_add_r:
  for +a: Nat
  for +b: Nat
  Le(a, Nat.add(a, b))

def le_add_r(a, b):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      le_add_r(p, b)

law le_add_l:
  for +a: Nat
  for +b: Nat
  Le(b, Nat.add(a, b))

def le_add_l(a, b):
  match a:
    case 0n:
      le_refl(b)
    case 1n+p:
      le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), le_add_l(p, b), le_succ(Nat.add(p, b)))

law le_add_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ac: Le(a, c)
  for bd: Le(b, d)
  Le(Nat.add(a, b), Nat.add(c, d))

def le_add_mono(a, b, c, d, ac, bd):
  match a c:
    case 0n c:
      le_trans(b, d, Nat.add(c, d), bd, le_add_l(c, d))
    case 1n+p 0n:
      absurd(Le(Nat.add(1n+p, b), Nat.add(0n, d)), bool_clash(ac))
    case 1n+p 1n+q:
      le_add_mono(p, b, q, d, ac, bd)

law not_lt_le:
  for +a: Nat
  for +b: Nat
  for f: Lt(a, b) -> Empty
  Le(b, a)

def not_lt_le(a, b, f):
  match a b:
    case a 0n:
      le_zero(a)
    case 0n 1n+q:
      absurd(Le(1n+q, 0n), f(le_zero(q)))
    case 1n+p 1n+q:
      not_lt_le(p, q, f)

law le_cases:
  for -R: Type
  for +a: Nat
  for +b: Nat
  for h: Le(a, b)
  for k1: Lt(a, b) -> R
  for k2: {a == b : Nat} -> R
  R

def le_cases(R, a, b, h, k1, k2):
  match a b:
    case 0n 0n:
      k2({==})
    case 0n 1n+q:
      k1(le_zero(q))
    case 1n+p 0n:
      absurd(R, bool_clash(h))
    case 1n+p 1n+q:
      le_cases(R, p, q, h, k1, e => k2(Equal.cong(Nat, Nat, x => 1n+x, p, q, e)))

law lt_irrefl:
  for +n: Nat
  for h: Lt(n, n)
  Empty

def lt_irrefl(n, h):
  match n:
    case 0n:
      bool_clash(h)
    case 1n+p:
      lt_irrefl(p, h)

law len_pos:
  for +e: Model.Expr
  Le(1n, Model.len(e))

def len_pos(e):
  match e:
    case Model.Lit{value}:
      {==}
    case Model.Var{name}:
      {==}
    case Model.Not{inner}:
      le_zero(Model.len(inner))
    case Model.And{l, r}:
      le_trans(1n, Model.len(l), Nat.add(Model.len(l), Model.len(r)), len_pos(l), le_add_r(Model.len(l), Model.len(r)))
    case Model.Or{l, r}:
      le_trans(1n, Model.len(l), Nat.add(Model.len(l), Model.len(r)), len_pos(l), le_add_r(Model.len(l), Model.len(r)))

def add_r(d: Nat, i: Nat) -> Nat:
  match d:
    case 0n:
      i
    case 1n+e:
      add_r(e, 1n+i)

law add_r_succ:
  for +d: Nat
  for +i: Nat
  {add_r(d, 1n+i) == 1n+add_r(d, i) : Nat}

def add_r_succ(d, i):
  match d:
    case 0n:
      {==}
    case 1n+e:
      add_r_succ(e, 1n+i)

law add_r_zero:
  for +d: Nat
  {add_r(d, 0n) == d : Nat}

def add_r_zero(d):
  match d:
    case 0n:
      {==}
    case 1n+e:
      %add_r_zero(e) : {add_r(e, 1n) == 1n+_ : Nat}
      add_r_succ(e, 0n)

law add_succ_right:
  for +i: Nat
  for +r: Nat
  {Nat.add(i, 1n+r) == 1n+Nat.add(i, r) : Nat}

def add_succ_right(i, r):
  match i:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+r), 1n+Nat.add(p, r), add_succ_right(p, r)) : {1n+_ == 1n+1n+Nat.add(p, r) : Nat}
      {==}

def subb(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Optimizer.mem(h, ys), subb(t, ys))

def noneb(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.not(Optimizer.mem(h, ys)), noneb(t, ys))

law or_false_r:
  for +a: Bool
  for +b: Bool
  for ea: {a == False{} : Bool}
  for e: {Bool.or(a, b) == True{} : Bool}
  {b == True{} : Bool}

def or_false_r(a, b, ea, e):
  match a:
    case False{}:
      e
    case True{}:
      absurd({b == True{} : Bool}, true_clash(ea))

law or_false_2:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_2(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      absurd({b == False{} : Bool}, true_clash(e))

law or_false_both:
  for +a: Bool
  for +b: Bool
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  {Bool.or(a, b) == False{} : Bool}

def or_false_both(a, b, ea, eb):
  match a:
    case False{}:
      eb
    case True{}:
      absurd({Bool.or(True{}, b) == False{} : Bool}, true_clash(ea))

law or_step:
  for +c: Bool
  for +m: Bool
  for +n: Bool
  for e: {Bool.or(c, m) == True{} : Bool}
  for ih: {m == True{} : Bool} -> {n == True{} : Bool}
  {Bool.or(c, n) == True{} : Bool}

def or_step(c, m, n, e, ih):
  match c:
    case False{}:
      ih(e)
    case True{}:
      {==}

law mem_head:
  for +h: String
  for +t: List<&2, String>
  {Optimizer.mem(h, h <> t) == True{} : Bool}

def mem_head(h, t):
  %Equal.sym(Bool, String.eq(h, h), True{}, string_eq_refl(h)) : {Bool.or(_, Optimizer.mem(h, t)) == True{} : Bool}
  {==}

law mem_tail:
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for e: {Optimizer.mem(x, t) == True{} : Bool}
  {Optimizer.mem(x, h <> t) == True{} : Bool}

def mem_tail(x, h, t, e):
  or_true_right(String.eq(x, h), Optimizer.mem(x, t), e)

law mem_cat_l:
  for +x: String
  for +a: List<&2, String>
  for +b: List<&2, String>
  for e: {Optimizer.mem(x, a) == True{} : Bool}
  {Optimizer.mem(x, Optimizer.cat(a, b)) == True{} : Bool}

def mem_cat_l(x, a, b, e):
  match a:
    case Nil{}:
      absurd({Optimizer.mem(x, b) == True{} : Bool}, bool_clash(e))
    case +h <> +t:
      or_step(String.eq(x, h), Optimizer.mem(x, t), Optimizer.mem(x, Optimizer.cat(t, b)), e, et => mem_cat_l(x, t, b, et))

law mem_cat_r:
  for +x: String
  for +a: List<&2, String>
  for +b: List<&2, String>
  for e: {Optimizer.mem(x, b) == True{} : Bool}
  {Optimizer.mem(x, Optimizer.cat(a, b)) == True{} : Bool}

def mem_cat_r(x, a, b, e):
  match a:
    case Nil{}:
      e
    case +h <> +t:
      or_true_right(String.eq(x, h), Optimizer.mem(x, Optimizer.cat(t, b)), mem_cat_r(x, t, b, e))

law cat_nil:
  for +a: List<&2, String>
  {Optimizer.cat(a, Nil{}) == a : List<&2, String>}

def cat_nil(a):
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, z => h <> z, Optimizer.cat(t, Nil{}), t, cat_nil(t))

def seen(names: List<&2, String>, +s: List<&2, String>) -> List<&2, String>:
  match names:
    case Nil{}:
      s
    case +h <> t:
      seen(t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s))

law uniq_cat_step:
  for +b: Bool
  for +h: String
  for +t: List<&2, String>
  for +ys: List<&2, String>
  for +s: List<&2, String>
  for ih_skip: {Optimizer.uniq(Optimizer.cat(t, ys), s) == Optimizer.cat(Optimizer.uniq(t, s), Optimizer.uniq(ys, seen(t, s))) : List<&2, String>}
  for ih_keep: {Optimizer.uniq(Optimizer.cat(t, ys), h <> s) == Optimizer.cat(Optimizer.uniq(t, h <> s), Optimizer.uniq(ys, seen(t, h <> s))) : List<&2, String>}
  {Optimizer.uniq.if(h, u => Optimizer.uniq(Optimizer.cat(t, ys), s), u => Optimizer.uniq(Optimizer.cat(t, ys), h <> s), b) == Optimizer.cat(Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b), Optimizer.uniq(ys, seen(t, Bool.pick(List<&2, String>, b, s, h <> s)))) : List<&2, String>}

def uniq_cat_step(b, h, t, ys, s, ih_skip, ih_keep):
  match b:
    case False{}:
      Equal.cong(List<&2, String>, List<&2, String>, z => h <> z, Optimizer.uniq(Optimizer.cat(t, ys), h <> s), Optimizer.cat(Optimizer.uniq(t, h <> s), Optimizer.uniq(ys, seen(t, h <> s))), ih_keep)
    case True{}:
      ih_skip

law uniq_cat:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +s: List<&2, String>
  {Optimizer.uniq(Optimizer.cat(xs, ys), s) == Optimizer.cat(Optimizer.uniq(xs, s), Optimizer.uniq(ys, seen(xs, s))) : List<&2, String>}

def uniq_cat(xs, ys, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      uniq_cat_step(Optimizer.mem(h, s), h, t, ys, s, uniq_cat(t, ys, s), uniq_cat(t, ys, h <> s))

law pick_keeps:
  for +x: String
  for +h: String
  for +s: List<&2, String>
  for +b: Bool
  for e: {Optimizer.mem(x, s) == True{} : Bool}
  {Optimizer.mem(x, Bool.pick(List<&2, String>, b, s, h <> s)) == True{} : Bool}

def pick_keeps(x, h, s, b, e):
  match b:
    case False{}:
      mem_tail(x, h, s, e)
    case True{}:
      e

law seen_keeps:
  for +x: String
  for +xs: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, s) == True{} : Bool}
  {Optimizer.mem(x, seen(xs, s)) == True{} : Bool}

def seen_keeps(x, xs, s, e):
  match xs:
    case Nil{}:
      e
    case +h <> +t:
      seen_keeps(x, t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s), pick_keeps(x, h, s, Optimizer.mem(h, s), e))

law pick_has:
  for +x: String
  for +h: String
  for +s: List<&2, String>
  for +b: Bool
  for xh: {x == h : String}
  for eb: {Optimizer.mem(h, s) == b : Bool}
  {Optimizer.mem(x, Bool.pick(List<&2, String>, b, s, h <> s)) == True{} : Bool}

def pick_has(x, h, s, b, xh, eb):
  match b:
    case False{}:
      %Equal.sym(String, x, h, xh) : {Optimizer.mem(_, h <> s) == True{} : Bool}
      mem_head(h, s)
    case True{}:
      %Equal.sym(String, x, h, xh) : {Optimizer.mem(_, s) == True{} : Bool}
      eb

law seen_has_step:
  for +c: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for ec: {String.eq(x, h) == c : Bool}
  for e: {Bool.or(c, Optimizer.mem(x, t)) == True{} : Bool}
  for ih: {Optimizer.mem(x, t) == True{} : Bool} -> {Optimizer.mem(x, seen(t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s))) == True{} : Bool}
  {Optimizer.mem(x, seen(t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s))) == True{} : Bool}

def seen_has_step(c, x, h, t, s, ec, e, ih):
  match c:
    case False{}:
      ih(e)
    case True{}:
      seen_keeps(x, t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s), pick_has(x, h, s, Optimizer.mem(h, s), string_eq_sound(x, h, ec), {==}))

law seen_has:
  for +x: String
  for +xs: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, xs) == True{} : Bool}
  {Optimizer.mem(x, seen(xs, s)) == True{} : Bool}

def seen_has(x, xs, s, e):
  match xs:
    case Nil{}:
      absurd({Optimizer.mem(x, s) == True{} : Bool}, bool_clash(e))
    case +h <> +t:
      seen_has_step(String.eq(x, h), x, h, t, s, {==}, e, et => seen_has(x, t, Bool.pick(List<&2, String>, Optimizer.mem(h, s), s, h <> s), et))

law uniq_fresh_keep:
  for +c: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for ec: {String.eq(x, h) == c : Bool}
  for eb: {Optimizer.mem(h, s) == False{} : Bool}
  for e: {Bool.or(c, Optimizer.mem(x, Optimizer.uniq(t, h <> s))) == True{} : Bool}
  for ih: {Optimizer.mem(x, Optimizer.uniq(t, h <> s)) == True{} : Bool} -> {Optimizer.mem(x, h <> s) == False{} : Bool}
  {Optimizer.mem(x, s) == False{} : Bool}

def uniq_fresh_keep(c, x, h, t, s, ec, eb, e, ih):
  match c:
    case False{}:
      or_false_2(String.eq(x, h), Optimizer.mem(x, s), ih(e))
    case True{}:
      %Equal.sym(String, x, h, string_eq_sound(x, h, ec)) : {Optimizer.mem(_, s) == False{} : Bool}
      eb

law uniq_fresh_step:
  for +b: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for eb: {Optimizer.mem(h, s) == b : Bool}
  for e: {Optimizer.mem(x, Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b)) == True{} : Bool}
  for ih_skip: {Optimizer.mem(x, Optimizer.uniq(t, s)) == True{} : Bool} -> {Optimizer.mem(x, s) == False{} : Bool}
  for ih_keep: {Optimizer.mem(x, Optimizer.uniq(t, h <> s)) == True{} : Bool} -> {Optimizer.mem(x, h <> s) == False{} : Bool}
  {Optimizer.mem(x, s) == False{} : Bool}

def uniq_fresh_step(b, x, h, t, s, eb, e, ih_skip, ih_keep):
  match b:
    case False{}:
      uniq_fresh_keep(String.eq(x, h), x, h, t, s, {==}, eb, e, ih_keep)
    case True{}:
      ih_skip(e)

law uniq_fresh:
  for +x: String
  for +ys: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, Optimizer.uniq(ys, s)) == True{} : Bool}
  {Optimizer.mem(x, s) == False{} : Bool}

def uniq_fresh(x, ys, s, e):
  match ys:
    case Nil{}:
      absurd({Optimizer.mem(x, s) == False{} : Bool}, bool_clash(e))
    case +h <> +t:
      uniq_fresh_step(Optimizer.mem(h, s), x, h, t, s, {==}, e, et => uniq_fresh(x, t, s, et), et => uniq_fresh(x, t, h <> s, et))

law uniq_sub_step:
  for +b: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b)) == True{} : Bool}
  for ih_skip: {Optimizer.mem(x, Optimizer.uniq(t, s)) == True{} : Bool} -> {Optimizer.mem(x, t) == True{} : Bool}
  for ih_keep: {Optimizer.mem(x, Optimizer.uniq(t, h <> s)) == True{} : Bool} -> {Optimizer.mem(x, t) == True{} : Bool}
  {Optimizer.mem(x, h <> t) == True{} : Bool}

def uniq_sub_step(b, x, h, t, s, e, ih_skip, ih_keep):
  match b:
    case False{}:
      or_step(String.eq(x, h), Optimizer.mem(x, Optimizer.uniq(t, h <> s)), Optimizer.mem(x, t), e, ih_keep)
    case True{}:
      mem_tail(x, h, t, ih_skip(e))

law uniq_sub:
  for +x: String
  for +ys: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, Optimizer.uniq(ys, s)) == True{} : Bool}
  {Optimizer.mem(x, ys) == True{} : Bool}

def uniq_sub(x, ys, s, e):
  match ys:
    case Nil{}:
      e
    case +h <> +t:
      uniq_sub_step(Optimizer.mem(h, s), x, h, t, s, e, et => uniq_sub(x, t, s, et), et => uniq_sub(x, t, h <> s, et))

law uniq_has_step:
  for +c: Bool
  for +b: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for ec: {String.eq(x, h) == c : Bool}
  for eb: {Optimizer.mem(h, s) == b : Bool}
  for e: {Bool.or(c, Optimizer.mem(x, t)) == True{} : Bool}
  for ns: {Optimizer.mem(x, s) == False{} : Bool}
  for ih_skip: {Optimizer.mem(x, t) == True{} : Bool} -> {Optimizer.mem(x, Optimizer.uniq(t, s)) == True{} : Bool}
  for ih_keep: {Optimizer.mem(x, t) == True{} : Bool} -> {Optimizer.mem(x, h <> s) == False{} : Bool} -> {Optimizer.mem(x, Optimizer.uniq(t, h <> s)) == True{} : Bool}
  {Optimizer.mem(x, Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b)) == True{} : Bool}

def uniq_has_step(c, b, x, h, t, s, ec, eb, e, ns, ih_skip, ih_keep):
  match c b:
    case True{} True{}:
      +nh = Equal.trans(Bool, Optimizer.mem(h, s), Optimizer.mem(x, s), False{}, Equal.cong(String, Bool, z => Optimizer.mem(z, s), h, x, Equal.sym(String, x, h, string_eq_sound(x, h, ec))), ns)
      absurd({Optimizer.mem(x, Optimizer.uniq(t, s)) == True{} : Bool}, bool_clash(Equal.trans(Bool, False{}, Optimizer.mem(h, s), True{}, Equal.sym(Bool, Optimizer.mem(h, s), False{}, nh), eb)))
    case True{} False{}:
      or_true_left(String.eq(x, h), Optimizer.mem(x, Optimizer.uniq(t, h <> s)), ec)
    case False{} True{}:
      ih_skip(e)
    case False{} False{}:
      or_true_right(String.eq(x, h), Optimizer.mem(x, Optimizer.uniq(t, h <> s)), ih_keep(e, or_false_both(String.eq(x, h), Optimizer.mem(x, s), ec, ns)))

law uniq_has:
  for +x: String
  for +ys: List<&2, String>
  for +s: List<&2, String>
  for e: {Optimizer.mem(x, ys) == True{} : Bool}
  for +ns: {Optimizer.mem(x, s) == False{} : Bool}
  {Optimizer.mem(x, Optimizer.uniq(ys, s)) == True{} : Bool}

def uniq_has(x, ys, s, e, ns):
  match ys:
    case Nil{}:
      absurd({Optimizer.mem(x, Nil{}) == True{} : Bool}, bool_clash(e))
    case +h <> +t:
      uniq_has_step(String.eq(x, h), Optimizer.mem(h, s), x, h, t, s, {==}, {==}, e, ns, et => uniq_has(x, t, s, et, ns), et => nhs => uniq_has(x, t, h <> s, et, nhs))

def filtS.put(+h: String, r: List<&2, String>, keep: Bool) -> List<&2, String>:
  match keep:
    case False{}:
      r
    case True{}:
      h <> r

def filtS(+names: List<&2, String>, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      filtS.put(h, filtS(names, t), Optimizer.mem(h, names))

law put_cat:
  for +h: String
  for +x: List<&2, String>
  for +y: List<&2, String>
  for +z: List<&2, String>
  for +k: Bool
  for ih: {x == Optimizer.cat(y, z) : List<&2, String>}
  {filtS.put(h, x, k) == Optimizer.cat(filtS.put(h, y, k), z) : List<&2, String>}

def put_cat(h, x, y, z, k, ih):
  match k:
    case False{}:
      ih
    case True{}:
      Equal.cong(List<&2, String>, List<&2, String>, w => h <> w, x, Optimizer.cat(y, z), ih)

law filtS_cat:
  for +names: List<&2, String>
  for +a: List<&2, String>
  for +b: List<&2, String>
  {filtS(names, Optimizer.cat(a, b)) == Optimizer.cat(filtS(names, a), filtS(names, b)) : List<&2, String>}

def filtS_cat(names, a, b):
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      put_cat(h, filtS(names, Optimizer.cat(t, b)), filtS(names, t), filtS(names, b), Optimizer.mem(h, names), filtS_cat(names, t, b))

law put_true:
  for +h: String
  for +x: List<&2, String>
  for +y: List<&2, String>
  for +k: Bool
  for ek: {k == True{} : Bool}
  for ih: {x == y : List<&2, String>}
  {filtS.put(h, x, k) == h <> y : List<&2, String>}

def put_true(h, x, y, k, ek, ih):
  match k:
    case False{}:
      absurd({x == h <> y : List<&2, String>}, bool_clash(ek))
    case True{}:
      Equal.cong(List<&2, String>, List<&2, String>, w => h <> w, x, y, ih)

law put_false:
  for +h: String
  for +x: List<&2, String>
  for +k: Bool
  for ek: {k == False{} : Bool}
  for ih: {x == Nil{} : List<&2, String>}
  {filtS.put(h, x, k) == Nil{} : List<&2, String>}

def put_false(h, x, k, ek, ih):
  match k:
    case False{}:
      ih
    case True{}:
      absurd({h <> x == Nil{} : List<&2, String>}, true_clash(ek))

law subb_cons:
  for +xs: List<&2, String>
  for +h: String
  for +ys: List<&2, String>
  for +s: {subb(xs, ys) == True{} : Bool}
  {subb(xs, h <> ys) == True{} : Bool}

def subb_cons(xs, h, ys, s):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      and_true(Optimizer.mem(x, h <> ys), subb(t, h <> ys), mem_tail(x, h, ys, and_true_left(Optimizer.mem(x, ys), subb(t, ys), s)), subb_cons(t, h, ys, and_true_right(Optimizer.mem(x, ys), subb(t, ys), s)))

law subb_refl:
  for +xs: List<&2, String>
  {subb(xs, xs) == True{} : Bool}

def subb_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Optimizer.mem(h, h <> t), subb(t, h <> t), mem_head(h, t), subb_cons(t, h, t, subb_refl(t)))

law subb_cat_l:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  for +s: {subb(xs, ys) == True{} : Bool}
  {subb(xs, Optimizer.cat(ys, zs)) == True{} : Bool}

def subb_cat_l(xs, ys, zs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Optimizer.mem(h, Optimizer.cat(ys, zs)), subb(t, Optimizer.cat(ys, zs)), mem_cat_l(h, ys, zs, and_true_left(Optimizer.mem(h, ys), subb(t, ys), s)), subb_cat_l(t, ys, zs, and_true_right(Optimizer.mem(h, ys), subb(t, ys), s)))

law subb_cat_r:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  for +s: {subb(xs, zs) == True{} : Bool}
  {subb(xs, Optimizer.cat(ys, zs)) == True{} : Bool}

def subb_cat_r(xs, ys, zs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Optimizer.mem(h, Optimizer.cat(ys, zs)), subb(t, Optimizer.cat(ys, zs)), mem_cat_r(h, ys, zs, and_true_left(Optimizer.mem(h, zs), subb(t, zs), s)), subb_cat_r(t, ys, zs, and_true_right(Optimizer.mem(h, zs), subb(t, zs), s)))

law subb_split_l:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  for +s: {subb(Optimizer.cat(xs, ys), zs) == True{} : Bool}
  {subb(xs, zs) == True{} : Bool}

def subb_split_l(xs, ys, zs, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Optimizer.mem(h, zs), subb(t, zs), and_true_left(Optimizer.mem(h, zs), subb(Optimizer.cat(t, ys), zs), s), subb_split_l(t, ys, zs, and_true_right(Optimizer.mem(h, zs), subb(Optimizer.cat(t, ys), zs), s)))

law subb_split_r:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  for +s: {subb(Optimizer.cat(xs, ys), zs) == True{} : Bool}
  {subb(ys, zs) == True{} : Bool}

def subb_split_r(xs, ys, zs, s):
  match xs:
    case Nil{}:
      s
    case +h <> +t:
      subb_split_r(t, ys, zs, and_true_right(Optimizer.mem(h, zs), subb(Optimizer.cat(t, ys), zs), s))

law sub_mem_step:
  for +c: Bool
  for +x: String
  for +h: String
  for +t: List<&2, String>
  for +ys: List<&2, String>
  for ec: {String.eq(x, h) == c : Bool}
  for s: {Bool.and(Optimizer.mem(h, ys), subb(t, ys)) == True{} : Bool}
  for e: {Bool.or(c, Optimizer.mem(x, t)) == True{} : Bool}
  for ih: {subb(t, ys) == True{} : Bool} -> {Optimizer.mem(x, t) == True{} : Bool} -> {Optimizer.mem(x, ys) == True{} : Bool}
  {Optimizer.mem(x, ys) == True{} : Bool}

def sub_mem_step(c, x, h, t, ys, ec, s, e, ih):
  match c:
    case False{}:
      ih(and_true_right(Optimizer.mem(h, ys), subb(t, ys), s), e)
    case True{}:
      %Equal.sym(String, x, h, string_eq_sound(x, h, ec)) : {Optimizer.mem(_, ys) == True{} : Bool}
      and_true_left(Optimizer.mem(h, ys), subb(t, ys), s)

law sub_mem:
  for +x: String
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for s: {subb(xs, ys) == True{} : Bool}
  for e: {Optimizer.mem(x, xs) == True{} : Bool}
  {Optimizer.mem(x, ys) == True{} : Bool}

def sub_mem(x, xs, ys, s, e):
  match xs:
    case Nil{}:
      absurd({Optimizer.mem(x, ys) == True{} : Bool}, bool_clash(e))
    case +h <> +t:
      sub_mem_step(String.eq(x, h), x, h, t, ys, {==}, s, e, st => et => sub_mem(x, t, ys, st, et))

law subb_uniq:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +s: {subb(xs, ys) == True{} : Bool}
  {subb(xs, Optimizer.uniq(ys, Nil{})) == True{} : Bool}

def subb_uniq(xs, ys, s):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Optimizer.mem(h, Optimizer.uniq(ys, Nil{})), subb(t, Optimizer.uniq(ys, Nil{})), uniq_has(h, ys, Nil{}, and_true_left(Optimizer.mem(h, ys), subb(t, ys), s), {==}), subb_uniq(t, ys, and_true_right(Optimizer.mem(h, ys), subb(t, ys), s)))

law filtS_all:
  for +names: List<&2, String>
  for +a: List<&2, String>
  for +s: {subb(a, names) == True{} : Bool}
  {filtS(names, a) == a : List<&2, String>}

def filtS_all(names, a, s):
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      put_true(h, filtS(names, t), t, Optimizer.mem(h, names), and_true_left(Optimizer.mem(h, names), subb(t, names), s), filtS_all(names, t, and_true_right(Optimizer.mem(h, names), subb(t, names), s)))

law not_true:
  for +b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_true(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, bool_clash(e))

law filtS_none:
  for +names: List<&2, String>
  for +a: List<&2, String>
  for +s: {noneb(a, names) == True{} : Bool}
  {filtS(names, a) == Nil{} : List<&2, String>}

def filtS_none(names, a, s):
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      put_false(h, filtS(names, t), Optimizer.mem(h, names), not_true(Optimizer.mem(h, names), and_true_left(Bool.not(Optimizer.mem(h, names)), noneb(t, names), s)), filtS_none(names, t, and_true_right(Bool.not(Optimizer.mem(h, names)), noneb(t, names), s)))

law uniq_seen_step:
  for +b: Bool
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for ih_skip: {subb(Optimizer.uniq(t, s), seen(t, s)) == True{} : Bool}
  for ih_keep: {subb(Optimizer.uniq(t, h <> s), seen(t, h <> s)) == True{} : Bool}
  {subb(Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b), seen(t, Bool.pick(List<&2, String>, b, s, h <> s))) == True{} : Bool}

def uniq_seen_step(b, h, t, s, ih_skip, ih_keep):
  match b:
    case False{}:
      and_true(Optimizer.mem(h, seen(t, h <> s)), subb(Optimizer.uniq(t, h <> s), seen(t, h <> s)), seen_keeps(h, t, h <> s, mem_head(h, s)), ih_keep)
    case True{}:
      ih_skip

law uniq_seen:
  for +ys: List<&2, String>
  for +s: List<&2, String>
  {subb(Optimizer.uniq(ys, s), seen(ys, s)) == True{} : Bool}

def uniq_seen(ys, s):
  match ys:
    case Nil{}:
      {==}
    case +h <> +t:
      uniq_seen_step(Optimizer.mem(h, s), h, t, s, uniq_seen(t, s), uniq_seen(t, h <> s))

law noneb_step:
  for +b: Bool
  for +c: Bool
  for +h: String
  for +t: List<&2, String>
  for +s: List<&2, String>
  for +v: List<&2, String>
  for eb: {Optimizer.mem(h, s) == b : Bool}
  for ec: {Optimizer.mem(h, v) == c : Bool}
  for sv: {subb(v, s) == True{} : Bool}
  for ih_skip: {noneb(Optimizer.uniq(t, s), v) == True{} : Bool}
  for ih_keep: {noneb(Optimizer.uniq(t, h <> s), v) == True{} : Bool}
  {noneb(Optimizer.uniq.if(h, u => Optimizer.uniq(t, s), u => Optimizer.uniq(t, h <> s), b), v) == True{} : Bool}

def noneb_step(b, c, h, t, s, v, eb, ec, sv, ih_skip, ih_keep):
  match b c:
    case True{} c:
      ih_skip
    case False{} True{}:
      absurd({noneb(h <> Optimizer.uniq(t, h <> s), v) == True{} : Bool}, bool_clash(Equal.trans(Bool, False{}, Optimizer.mem(h, s), True{}, Equal.sym(Bool, Optimizer.mem(h, s), False{}, eb), sub_mem(h, v, s, sv, ec))))
    case False{} False{}:
      and_true(Bool.not(Optimizer.mem(h, v)), noneb(Optimizer.uniq(t, h <> s), v), Equal.cong(Bool, Bool, z => Bool.not(z), Optimizer.mem(h, v), False{}, ec), ih_keep)

law noneb_uniq:
  for +zs: List<&2, String>
  for +s: List<&2, String>
  for +v: List<&2, String>
  for +sv: {subb(v, s) == True{} : Bool}
  {noneb(Optimizer.uniq(zs, s), v) == True{} : Bool}

def noneb_uniq(zs, s, v, sv):
  match zs:
    case Nil{}:
      {==}
    case +h <> +t:
      noneb_step(Optimizer.mem(h, s), Optimizer.mem(h, v), h, t, s, v, {==}, {==}, sv, noneb_uniq(t, s, v, sv), noneb_uniq(t, h <> s, v, subb_cons(v, h, s, sv)))

law uniq_prefix:
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  {filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(Optimizer.cat(ys, zs), Nil{})) == Optimizer.uniq(ys, Nil{}) : List<&2, String>}

def uniq_prefix(ys, zs):
  %Equal.sym(List<&2, String>, Optimizer.uniq(Optimizer.cat(ys, zs), Nil{}), Optimizer.cat(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{}))), uniq_cat(ys, zs, Nil{})) : {filtS(Optimizer.uniq(ys, Nil{}), _) == Optimizer.uniq(ys, Nil{}) : List<&2, String>}
  %Equal.sym(List<&2, String>, filtS(Optimizer.uniq(ys, Nil{}), Optimizer.cat(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})))), Optimizer.cat(filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(ys, Nil{})), filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})))), filtS_cat(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})))) : {_ == Optimizer.uniq(ys, Nil{}) : List<&2, String>}
  %Equal.sym(List<&2, String>, filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(ys, Nil{})), Optimizer.uniq(ys, Nil{}), filtS_all(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(ys, Nil{}), subb_refl(Optimizer.uniq(ys, Nil{})))) : {Optimizer.cat(_, filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})))) == Optimizer.uniq(ys, Nil{}) : List<&2, String>}
  %Equal.sym(List<&2, String>, filtS(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{}))), Nil{}, filtS_none(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})), noneb_uniq(zs, seen(ys, Nil{}), Optimizer.uniq(ys, Nil{}), uniq_seen(ys, Nil{})))) : {Optimizer.cat(Optimizer.uniq(ys, Nil{}), _) == Optimizer.uniq(ys, Nil{}) : List<&2, String>}
  cat_nil(Optimizer.uniq(ys, Nil{}))

law uniq_prefix_sub:
  for +ys: List<&2, String>
  for +zs: List<&2, String>
  {subb(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(Optimizer.cat(ys, zs), Nil{})) == True{} : Bool}

def uniq_prefix_sub(ys, zs):
  %Equal.sym(List<&2, String>, Optimizer.uniq(Optimizer.cat(ys, zs), Nil{}), Optimizer.cat(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{}))), uniq_cat(ys, zs, Nil{})) : {subb(Optimizer.uniq(ys, Nil{}), _) == True{} : Bool}
  subb_cat_l(Optimizer.uniq(ys, Nil{}), Optimizer.uniq(ys, Nil{}), Optimizer.uniq(zs, seen(ys, Nil{})), subb_refl(Optimizer.uniq(ys, Nil{})))

def over(+names: List<&2, String>, expr: Model.Expr) -> Bool:
  match expr:
    case Model.Lit{value}:
      True{}
    case Model.Var{name}:
      Optimizer.mem(name, names)
    case Model.Not{inner}:
      over(names, inner)
    case Model.And{left, right}:
      Bool.and(over(names, left), over(names, right))
    case Model.Or{left, right}:
      Bool.and(over(names, left), over(names, right))

def pure(expr: Model.Expr) -> Bool:
  match expr:
    case Model.Lit{value}:
      False{}
    case Model.Var{name}:
      True{}
    case Model.Not{inner}:
      pure(inner)
    case Model.And{left, right}:
      Bool.and(pure(left), pure(right))
    case Model.Or{left, right}:
      Bool.and(pure(left), pure(right))

def is_lit(expr: Model.Expr) -> Bool:
  match expr:
    case Model.Lit{value}:
      True{}
    case Model.Var{name}:
      False{}
    case Model.Not{inner}:
      False{}
    case Model.And{left, right}:
      False{}
    case Model.Or{left, right}:
      False{}

def ext(names: List<&2, String>, +env: Model.Env, acc: Model.Env) -> Model.Env:
  match names:
    case Nil{}:
      acc
    case +h <> t:
      ext(t, env, Model.EnvCons{h, Model.lookup(env, h), acc})

law and_cong:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for ac: {a == c : Bool}
  for bd: {b == d : Bool}
  {Bool.and(a, b) == Bool.and(c, d) : Bool}

def and_cong(a, b, c, d, ac, bd):
  %ac : {Bool.and(a, b) == Bool.and(_, d) : Bool}
  %bd : {Bool.and(a, b) == Bool.and(a, _) : Bool}
  {==}

law or_cong:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for ac: {a == c : Bool}
  for bd: {b == d : Bool}
  {Bool.or(a, b) == Bool.or(c, d) : Bool}

def or_cong(a, b, c, d, ac, bd):
  %ac : {Bool.or(a, b) == Bool.or(_, d) : Bool}
  %bd : {Bool.or(a, b) == Bool.or(a, _) : Bool}
  {==}

law not_cong:
  for +a: Bool
  for +c: Bool
  for ac: {a == c : Bool}
  {Bool.not(a) == Bool.not(c) : Bool}

def not_cong(a, c, ac):
  %ac : {Bool.not(a) == Bool.not(_) : Bool}
  {==}

law lookup_step:
  for +c: Bool
  for +m: Bool
  for +ln: Bool
  for +lh: Bool
  for +la: Bool
  for hc: {c == True{} : Bool} -> {lh == ln : Bool}
  {Bool.pick(Bool, m, ln, Bool.pick(Bool, c, lh, la)) == Bool.pick(Bool, Bool.or(c, m), ln, la) : Bool}

def lookup_step(c, m, ln, lh, la, hc):
  match c m:
    case True{} True{}:
      {==}
    case True{} False{}:
      hc({==})
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

law lookup_ext:
  for +names: List<&2, String>
  for +env: Model.Env
  for +acc: Model.Env
  for +n: String
  {Model.lookup(ext(names, env, acc), n) == Bool.pick(Bool, Optimizer.mem(n, names), Model.lookup(env, n), Model.lookup(acc, n)) : Bool}

def lookup_ext(names, env, acc, n):
  match names:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.trans(Bool, Model.lookup(ext(t, env, Model.EnvCons{h, Model.lookup(env, h), acc}), n), Bool.pick(Bool, Optimizer.mem(n, t), Model.lookup(env, n), Model.lookup(Model.EnvCons{h, Model.lookup(env, h), acc}, n)), Bool.pick(Bool, Optimizer.mem(n, h <> t), Model.lookup(env, n), Model.lookup(acc, n)), lookup_ext(t, env, Model.EnvCons{h, Model.lookup(env, h), acc}, n), lookup_step(String.eq(n, h), Optimizer.mem(n, t), Model.lookup(env, n), Model.lookup(env, h), Model.lookup(acc, n), e => Equal.cong(String, Bool, z => Model.lookup(env, z), h, n, Equal.sym(String, n, h, string_eq_sound(n, h, e)))))

law pick_true_eq:
  for +b: Bool
  for +x: Bool
  for +y: Bool
  for hb: {b == True{} : Bool}
  {Bool.pick(Bool, b, x, y) == x : Bool}

def pick_true_eq(b, x, y, hb):
  match b:
    case False{}:
      absurd({y == x : Bool}, bool_clash(hb))
    case True{}:
      {==}

law eval_ext:
  for +names: List<&2, String>
  for +env: Model.Env
  for +e: Model.Expr
  for +ov: {over(names, e) == True{} : Bool}
  {Model.eval(e, ext(names, env, Model.EnvNil{})) == Model.eval(e, env) : Bool}

def eval_ext(names, env, e, ov):
  match e:
    case Model.Lit{value}:
      {==}
    case Model.Var{n}:
      Equal.trans(Bool, Model.lookup(ext(names, env, Model.EnvNil{}), n), Bool.pick(Bool, Optimizer.mem(n, names), Model.lookup(env, n), Model.lookup(Model.EnvNil{}, n)), Model.lookup(env, n), lookup_ext(names, env, Model.EnvNil{}, n), pick_true_eq(Optimizer.mem(n, names), Model.lookup(env, n), Model.lookup(Model.EnvNil{}, n), ov))
    case Model.Not{i}:
      not_cong(Model.eval(i, ext(names, env, Model.EnvNil{})), Model.eval(i, env), eval_ext(names, env, i, ov))
    case Model.And{l, r}:
      and_cong(Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{})), Model.eval(l, env), Model.eval(r, env), eval_ext(names, env, l, and_true_left(over(names, l), over(names, r), ov)), eval_ext(names, env, r, and_true_right(over(names, l), over(names, r), ov)))
    case Model.Or{l, r}:
      or_cong(Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{})), Model.eval(l, env), Model.eval(r, env), eval_ext(names, env, l, and_true_left(over(names, l), over(names, r), ov)), eval_ext(names, env, r, and_true_right(over(names, l), over(names, r), ov)))

law xnor_sound:
  for +x: Bool
  for +y: Bool
  for e: {Bool.not(Bool.xor(x, y)) == True{} : Bool}
  {x == y : Bool}

def xnor_sound(x, y, e):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({False{} == True{} : Bool}, bool_clash(e))
    case True{} False{}:
      absurd({True{} == False{} : Bool}, bool_clash(e))
    case True{} True{}:
      {==}

law xnor_refl:
  for +x: Bool
  {Bool.not(Bool.xor(x, x)) == True{} : Bool}

def xnor_refl(x):
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

law agree_at:
  for +v: Bool
  for +x: Bool
  for +y: Bool
  for h: {Bool.and(x, y) == True{} : Bool}
  {Bool.pick(Bool, v, x, y) == True{} : Bool}

def agree_at(v, x, y, h):
  match v:
    case False{}:
      and_true_right(x, y, h)
    case True{}:
      and_true_left(x, y, h)

law agree_pick:
  for +v: Bool
  for +h: String
  for +t: List<&2, String>
  for +acc: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {Bool.and(Optimizer.agree(t, Model.EnvCons{h, True{}, acc}, a, b), Optimizer.agree(t, Model.EnvCons{h, False{}, acc}, a, b)) == True{} : Bool}
  {Optimizer.agree(t, Model.EnvCons{h, v, acc}, a, b) == True{} : Bool}

def agree_pick(v, h, t, acc, a, b, e):
  match v:
    case False{}:
      and_true_right(Optimizer.agree(t, Model.EnvCons{h, True{}, acc}, a, b), Optimizer.agree(t, Model.EnvCons{h, False{}, acc}, a, b), e)
    case True{}:
      and_true_left(Optimizer.agree(t, Model.EnvCons{h, True{}, acc}, a, b), Optimizer.agree(t, Model.EnvCons{h, False{}, acc}, a, b), e)

law agree_sound:
  for +names: List<&2, String>
  for +acc: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for +h: {Optimizer.agree(names, acc, a, b) == True{} : Bool}
  for +env: Model.Env
  {Model.eval(a, ext(names, env, acc)) == Model.eval(b, ext(names, env, acc)) : Bool}

def agree_sound(names, acc, a, b, h, env):
  match names:
    case Nil{}:
      xnor_sound(Model.eval(a, acc), Model.eval(b, acc), h)
    case +n <> +t:
      agree_sound(t, Model.EnvCons{n, Model.lookup(env, n), acc}, a, b, agree_pick(Model.lookup(env, n), n, t, acc, a, b, h), env)

law agree_eval:
  for +names: List<&2, String>
  for +a: Model.Expr
  for +b: Model.Expr
  for +oa: {over(names, a) == True{} : Bool}
  for +ob: {over(names, b) == True{} : Bool}
  for +h: {Optimizer.agree(names, Model.EnvNil{}, a, b) == True{} : Bool}
  for +env: Model.Env
  {Model.eval(a, env) == Model.eval(b, env) : Bool}

def agree_eval(names, a, b, oa, ob, h, env):
  Equal.trans(Bool, Model.eval(a, env), Model.eval(a, ext(names, env, Model.EnvNil{})), Model.eval(b, env), Equal.sym(Bool, Model.eval(a, ext(names, env, Model.EnvNil{})), Model.eval(a, env), eval_ext(names, env, a, oa)), Equal.trans(Bool, Model.eval(a, ext(names, env, Model.EnvNil{})), Model.eval(b, ext(names, env, Model.EnvNil{})), Model.eval(b, env), agree_sound(names, Model.EnvNil{}, a, b, h, env), eval_ext(names, env, b, ob)))

def cex(names: List<&2, String>, +acc: Model.Env, +a: Model.Expr, +b: Model.Expr) -> Model.Env:
  match names:
    case Nil{}:
      acc
    case +h <> +t:
      Bool.pick(Model.Env, Optimizer.agree(t, Model.EnvCons{h, True{}, acc}, a, b), cex(t, Model.EnvCons{h, False{}, acc}, a, b), cex(t, Model.EnvCons{h, True{}, acc}, a, b))

law cex_step:
  for +c1: Bool
  for +c2: Bool
  for +x: Model.Env
  for +y: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for ihf: {c2 == False{} : Bool} -> {Model.eval(a, x) == Model.eval(b, x) : Bool} -> Empty
  for iht: {c1 == False{} : Bool} -> {Model.eval(a, y) == Model.eval(b, y) : Bool} -> Empty
  for e: {Bool.and(c1, c2) == False{} : Bool}
  for h: {Model.eval(a, Bool.pick(Model.Env, c1, x, y)) == Model.eval(b, Bool.pick(Model.Env, c1, x, y)) : Bool}
  Empty

def cex_step(c1, c2, x, y, a, b, ihf, iht, e, h):
  match c1:
    case False{}:
      iht({==}, h)
    case True{}:
      ihf(e, h)

law cex_spec:
  for +names: List<&2, String>
  for +acc: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for e: {Optimizer.agree(names, acc, a, b) == False{} : Bool}
  for h: {Model.eval(a, cex(names, acc, a, b)) == Model.eval(b, cex(names, acc, a, b)) : Bool}
  Empty

def cex_spec(names, acc, a, b, e, h):
  match names:
    case Nil{}:
      bool_clash(Equal.trans(Bool, False{}, Bool.not(Bool.xor(Model.eval(a, acc), Model.eval(b, acc))), True{}, Equal.sym(Bool, Bool.not(Bool.xor(Model.eval(a, acc), Model.eval(b, acc))), False{}, e), Equal.trans(Bool, Bool.not(Bool.xor(Model.eval(a, acc), Model.eval(b, acc))), Bool.not(Bool.xor(Model.eval(b, acc), Model.eval(b, acc))), True{}, Equal.cong(Bool, Bool, z => Bool.not(Bool.xor(z, Model.eval(b, acc))), Model.eval(a, acc), Model.eval(b, acc), h), xnor_refl(Model.eval(b, acc)))))
    case +n <> +t:
      cex_step(Optimizer.agree(t, Model.EnvCons{n, True{}, acc}, a, b), Optimizer.agree(t, Model.EnvCons{n, False{}, acc}, a, b), cex(t, Model.EnvCons{n, False{}, acc}, a, b), cex(t, Model.EnvCons{n, True{}, acc}, a, b), a, b, ef => hf => cex_spec(t, Model.EnvCons{n, False{}, acc}, a, b, ef, hf), et => ht => cex_spec(t, Model.EnvCons{n, True{}, acc}, a, b, et, ht), e, h)

law agree_by_step:
  for +v: Bool
  for +names: List<&2, String>
  for +acc: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for ev: {Optimizer.agree(names, acc, a, b) == v : Bool}
  for k: {Model.eval(a, cex(names, acc, a, b)) == Model.eval(b, cex(names, acc, a, b)) : Bool}
  {v == True{} : Bool}

def agree_by_step(v, names, acc, a, b, ev, k):
  match v:
    case False{}:
      absurd({False{} == True{} : Bool}, cex_spec(names, acc, a, b, ev, k))
    case True{}:
      {==}

law agree_by:
  for +names: List<&2, String>
  for +acc: Model.Env
  for +a: Model.Expr
  for +b: Model.Expr
  for k: @w: Model.Env -> {Model.eval(a, w) == Model.eval(b, w) : Bool}
  {Optimizer.agree(names, acc, a, b) == True{} : Bool}

def agree_by(names, acc, a, b, k):
  agree_by_step(Optimizer.agree(names, acc, a, b), names, acc, a, b, {==}, k(cex(names, acc, a, b)))

law over_of_sub:
  for +u: List<&2, String>
  for +e: Model.Expr
  for +s: {subb(Optimizer.vars(e), u) == True{} : Bool}
  {over(u, e) == True{} : Bool}

def over_of_sub(u, e, s):
  match e:
    case Model.Lit{value}:
      {==}
    case Model.Var{n}:
      and_true_left(Optimizer.mem(n, u), True{}, s)
    case Model.Not{i}:
      over_of_sub(u, i, s)
    case Model.And{l, r}:
      and_true(over(u, l), over(u, r), over_of_sub(u, l, subb_split_l(Optimizer.vars(l), Optimizer.vars(r), u, s)), over_of_sub(u, r, subb_split_r(Optimizer.vars(l), Optimizer.vars(r), u, s)))
    case Model.Or{l, r}:
      and_true(over(u, l), over(u, r), over_of_sub(u, l, subb_split_l(Optimizer.vars(l), Optimizer.vars(r), u, s)), over_of_sub(u, r, subb_split_r(Optimizer.vars(l), Optimizer.vars(r), u, s)))

law over_vars:
  for +e: Model.Expr
  {over(Optimizer.uniq(Optimizer.vars(e), Nil{}), e) == True{} : Bool}

def over_vars(e):
  over_of_sub(Optimizer.uniq(Optimizer.vars(e), Nil{}), e, subb_uniq(Optimizer.vars(e), Optimizer.vars(e), subb_refl(Optimizer.vars(e))))

law over_mono:
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +e: Model.Expr
  for +s: {subb(v, w) == True{} : Bool}
  for +o: {over(v, e) == True{} : Bool}
  {over(w, e) == True{} : Bool}

def over_mono(v, w, e, s, o):
  match e:
    case Model.Lit{value}:
      {==}
    case Model.Var{n}:
      sub_mem(n, v, w, s, o)
    case Model.Not{i}:
      over_mono(v, w, i, s, o)
    case Model.And{l, r}:
      and_true(over(w, l), over(w, r), over_mono(v, w, l, s, and_true_left(over(v, l), over(v, r), o)), over_mono(v, w, r, s, and_true_right(over(v, l), over(v, r), o)))
    case Model.Or{l, r}:
      and_true(over(w, l), over(w, r), over_mono(v, w, l, s, and_true_left(over(v, l), over(v, r), o)), over_mono(v, w, r, s, and_true_right(over(v, l), over(v, r), o)))

def red.var(+n: String, b: Bool) -> Model.Expr:
  match b:
    case False{}:
      Model.Lit{False{}}
    case True{}:
      Model.Var{n}

def red.not(e: Model.Expr) -> Model.Expr:
  match e:
    case Model.Lit{v}:
      Model.Lit{Bool.not(v)}
    case Model.Var{n}:
      Model.Not{Model.Var{n}}
    case Model.Not{i}:
      Model.Not{Model.Not{i}}
    case Model.And{l, r}:
      Model.Not{Model.And{l, r}}
    case Model.Or{l, r}:
      Model.Not{Model.Or{l, r}}

def red.and.r(a: Model.Expr, b: Model.Expr) -> Model.Expr:
  match b:
    case Model.Lit{v}:
      match v:
        case False{}:
          Model.Lit{False{}}
        case True{}:
          a
    case Model.Var{n}:
      Model.And{a, Model.Var{n}}
    case Model.Not{i}:
      Model.And{a, Model.Not{i}}
    case Model.And{l, r}:
      Model.And{a, Model.And{l, r}}
    case Model.Or{l, r}:
      Model.And{a, Model.Or{l, r}}

def red.and(a: Model.Expr, b: Model.Expr) -> Model.Expr:
  match a:
    case Model.Lit{v}:
      match v:
        case False{}:
          Model.Lit{False{}}
        case True{}:
          b
    case Model.Var{n}:
      red.and.r(Model.Var{n}, b)
    case Model.Not{i}:
      red.and.r(Model.Not{i}, b)
    case Model.And{l, r}:
      red.and.r(Model.And{l, r}, b)
    case Model.Or{l, r}:
      red.and.r(Model.Or{l, r}, b)

def red.or.r(a: Model.Expr, b: Model.Expr) -> Model.Expr:
  match b:
    case Model.Lit{v}:
      match v:
        case True{}:
          Model.Lit{True{}}
        case False{}:
          a
    case Model.Var{n}:
      Model.Or{a, Model.Var{n}}
    case Model.Not{i}:
      Model.Or{a, Model.Not{i}}
    case Model.And{l, r}:
      Model.Or{a, Model.And{l, r}}
    case Model.Or{l, r}:
      Model.Or{a, Model.Or{l, r}}

def red.or(a: Model.Expr, b: Model.Expr) -> Model.Expr:
  match a:
    case Model.Lit{v}:
      match v:
        case True{}:
          Model.Lit{True{}}
        case False{}:
          b
    case Model.Var{n}:
      red.or.r(Model.Var{n}, b)
    case Model.Not{i}:
      red.or.r(Model.Not{i}, b)
    case Model.And{l, r}:
      red.or.r(Model.And{l, r}, b)
    case Model.Or{l, r}:
      red.or.r(Model.Or{l, r}, b)

def red(+names: List<&2, String>, e: Model.Expr) -> Model.Expr:
  match e:
    case Model.Lit{v}:
      Model.Lit{v}
    case Model.Var{+n}:
      red.var(n, Optimizer.mem(n, names))
    case Model.Not{i}:
      red.not(red(names, i))
    case Model.And{l, r}:
      red.and(red(names, l), red(names, r))
    case Model.Or{l, r}:
      red.or(red(names, l), red(names, r))

def good(+names: List<&2, String>, +x: Model.Expr) -> Bool:
  Bool.or(is_lit(x), Bool.and(pure(x), over(names, x)))

law eval_red_var:
  for +n: String
  for +b: Bool
  for +env: Model.Env
  {Model.eval(red.var(n, b), env) == Bool.pick(Bool, b, Model.lookup(env, n), False{}) : Bool}

def eval_red_var(n, b, env):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law eval_red_not:
  for +x: Model.Expr
  for +env: Model.Env
  {Model.eval(red.not(x), env) == Bool.not(Model.eval(x, env)) : Bool}

def eval_red_not(x, env):
  match x:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law len_red_var:
  for +n: String
  for +b: Bool
  Le(Model.len(red.var(n, b)), 1n)

def len_red_var(n, b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law len_red_not:
  for +x: Model.Expr
  Le(Model.len(red.not(x)), 1n+Model.len(x))

def len_red_not(x):
  match x:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      le_refl(Model.len(Model.Not{Model.Not{i}}))
    case Model.And{l, r}:
      le_refl(Model.len(Model.Not{Model.And{l, r}}))
    case Model.Or{l, r}:
      le_refl(Model.len(Model.Not{Model.Or{l, r}}))

law add_one_r:
  for +n: Nat
  {Nat.add(n, 1n) == 1n+n : Nat}

def add_one_r(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n), 1n+p, add_one_r(p))

law good_red_var:
  for +names: List<&2, String>
  for +n: String
  for +b: Bool
  for eb: {Optimizer.mem(n, names) == b : Bool}
  {good(names, red.var(n, b)) == True{} : Bool}

def good_red_var(names, n, b, eb):
  match b:
    case False{}:
      {==}
    case True{}:
      eb

law good_red_not:
  for +names: List<&2, String>
  for +x: Model.Expr
  for gx: {good(names, x) == True{} : Bool}
  {good(names, red.not(x)) == True{} : Bool}

def good_red_not(names, x, gx):
  match x:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      gx
    case Model.Not{i}:
      gx
    case Model.And{l, r}:
      gx
    case Model.Or{l, r}:
      gx

law and4:
  for +pa: Bool
  for +oa: Bool
  for +pb: Bool
  for +ob: Bool
  for +ha: {Bool.and(pa, oa) == True{} : Bool}
  for +hb: {Bool.and(pb, ob) == True{} : Bool}
  {Bool.and(Bool.and(pa, pb), Bool.and(oa, ob)) == True{} : Bool}

def and4(pa, oa, pb, ob, ha, hb):
  and_true(Bool.and(pa, pb), Bool.and(oa, ob), and_true(pa, pb, and_true_left(pa, oa, ha), and_true_left(pb, ob, hb)), and_true(oa, ob, and_true_right(pa, oa, ha), and_true_right(pb, ob, hb)))

law good_pure:
  for +names: List<&2, String>
  for +x: Model.Expr
  for +g: {good(names, x) == True{} : Bool}
  for +nl: {is_lit(x) == False{} : Bool}
  {pure(x) == True{} : Bool}

def good_pure(names, x, g, nl):
  and_true_left(pure(x), over(names, x), or_false_r(is_lit(x), Bool.and(pure(x), over(names, x)), nl, g))

law good_over:
  for +names: List<&2, String>
  for +x: Model.Expr
  for +g: {good(names, x) == True{} : Bool}
  for +nl: {is_lit(x) == False{} : Bool}
  {over(names, x) == True{} : Bool}

def good_over(names, x, g, nl):
  and_true_right(pure(x), over(names, x), or_false_r(is_lit(x), Bool.and(pure(x), over(names, x)), nl, g))

law strict_var:
  for +n: String
  for +b: Bool
  for no: {b == False{} : Bool}
  for nl: {is_lit(red.var(n, b)) == False{} : Bool}
  Lt(Model.len(red.var(n, b)), 1n)

def strict_var(n, b, no, nl):
  match b:
    case False{}:
      absurd(Lt(1n, 1n), true_clash(nl))
    case True{}:
      absurd(Lt(1n, 1n), true_clash(no))

law nl_not:
  for +x: Model.Expr
  for h: {is_lit(red.not(x)) == False{} : Bool}
  {is_lit(x) == False{} : Bool}

def nl_not(x, h):
  match x:
    case Model.Lit{v}:
      absurd({True{} == False{} : Bool}, true_clash(h))
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law len_not_nl:
  for +x: Model.Expr
  for h: {is_lit(red.not(x)) == False{} : Bool}
  {Model.len(red.not(x)) == 1n+Model.len(x) : Nat}

def len_not_nl(x, h):
  match x:
    case Model.Lit{v}:
      absurd({1n == 2n : Nat}, true_clash(h))
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law eval_red_and_r:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  {Model.eval(red.and.r(a, b), env) == Bool.and(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_red_and_r(a, b, env):
  match b:
    case Model.Lit{v}:
      match v:
        case False{}:
          Equal.sym(Bool, Bool.and(Model.eval(a, env), False{}), False{}, bool_and_false(Model.eval(a, env)))
        case True{}:
          Equal.sym(Bool, Bool.and(Model.eval(a, env), True{}), Model.eval(a, env), bool_and_true(Model.eval(a, env)))
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law eval_red_and:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  {Model.eval(red.and(a, b), env) == Bool.and(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_red_and(a, b, env):
  match a:
    case Model.Lit{v}:
      match v:
        case False{}:
          {==}
        case True{}:
          {==}
    case Model.Var{n}:
      eval_red_and_r(Model.Var{n}, b, env)
    case Model.Not{i}:
      eval_red_and_r(Model.Not{i}, b, env)
    case Model.And{l, r}:
      eval_red_and_r(Model.And{l, r}, b, env)
    case Model.Or{l, r}:
      eval_red_and_r(Model.Or{l, r}, b, env)

law len_red_and_r:
  for +a: Model.Expr
  for +b: Model.Expr
  Le(Model.len(red.and.r(a, b)), Nat.add(Model.len(a), Model.len(b)))

def len_red_and_r(a, b):
  match b:
    case Model.Lit{v}:
      match v:
        case False{}:
          le_trans(1n, Model.len(a), Nat.add(Model.len(a), 1n), len_pos(a), le_add_r(Model.len(a), 1n))
        case True{}:
          le_add_r(Model.len(a), 1n)
    case Model.Var{n}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Var{n})))
    case Model.Not{i}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Not{i})))
    case Model.And{l, r}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.And{l, r})))
    case Model.Or{l, r}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Or{l, r})))

law len_red_and:
  for +a: Model.Expr
  for +b: Model.Expr
  Le(Model.len(red.and(a, b)), Nat.add(Model.len(a), Model.len(b)))

def len_red_and(a, b):
  match a:
    case Model.Lit{v}:
      match v:
        case False{}:
          le_zero(Model.len(b))
        case True{}:
          le_succ(Model.len(b))
    case Model.Var{n}:
      len_red_and_r(Model.Var{n}, b)
    case Model.Not{i}:
      len_red_and_r(Model.Not{i}, b)
    case Model.And{l, r}:
      len_red_and_r(Model.And{l, r}, b)
    case Model.Or{l, r}:
      len_red_and_r(Model.Or{l, r}, b)

law good_red_and_r:
  for +names: List<&2, String>
  for +a: Model.Expr
  for +b: Model.Expr
  for +na: {is_lit(a) == False{} : Bool}
  for +ga: {good(names, a) == True{} : Bool}
  for +gb: {good(names, b) == True{} : Bool}
  {good(names, red.and.r(a, b)) == True{} : Bool}

def good_red_and_r(names, a, b, na, ga, gb):
  match b:
    case Model.Lit{v}:
      match v:
        case False{}:
          {==}
        case True{}:
          ga
    case Model.Var{n}:
      and4(pure(a), over(names, a), pure(Model.Var{n}), over(names, Model.Var{n}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.Not{i}:
      and4(pure(a), over(names, a), pure(Model.Not{i}), over(names, Model.Not{i}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.And{l, r}:
      and4(pure(a), over(names, a), pure(Model.And{l, r}), over(names, Model.And{l, r}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.Or{l, r}:
      and4(pure(a), over(names, a), pure(Model.Or{l, r}), over(names, Model.Or{l, r}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)

law good_red_and:
  for +names: List<&2, String>
  for +a: Model.Expr
  for +b: Model.Expr
  for +ga: {good(names, a) == True{} : Bool}
  for +gb: {good(names, b) == True{} : Bool}
  {good(names, red.and(a, b)) == True{} : Bool}

def good_red_and(names, a, b, ga, gb):
  match a:
    case Model.Lit{v}:
      match v:
        case False{}:
          {==}
        case True{}:
          gb
    case Model.Var{n}:
      good_red_and_r(names, Model.Var{n}, b, {==}, ga, gb)
    case Model.Not{i}:
      good_red_and_r(names, Model.Not{i}, b, {==}, ga, gb)
    case Model.And{l, r}:
      good_red_and_r(names, Model.And{l, r}, b, {==}, ga, gb)
    case Model.Or{l, r}:
      good_red_and_r(names, Model.Or{l, r}, b, {==}, ga, gb)

law strict_and_r:
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for hx: Lt(Model.len(x), p)
  for ly: Le(Model.len(y), q)
  for nl: {is_lit(red.and.r(x, y)) == False{} : Bool}
  Lt(Model.len(red.and.r(x, y)), Nat.add(p, q))

def strict_and_r(x, y, p, q, hx, ly, nl):
  match y:
    case Model.Lit{v}:
      match v:
        case False{}:
          absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
        case True{}:
          le_trans(1n+Model.len(x), p, Nat.add(p, q), hx, le_add_r(p, q))
    case Model.Var{n}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Var{n}), p, q, hx, ly)
    case Model.Not{i}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Not{i}), p, q, hx, ly)
    case Model.And{l, r}:
      le_add_mono(1n+Model.len(x), Model.len(Model.And{l, r}), p, q, hx, ly)
    case Model.Or{l, r}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Or{l, r}), p, q, hx, ly)

law strict_and_l:
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for lx: Le(Model.len(x), p)
  for pq: Le(1n, q)
  for hy: {is_lit(y) == False{} : Bool} -> Lt(Model.len(y), q)
  for nl: {is_lit(red.and.r(x, y)) == False{} : Bool}
  Lt(Model.len(red.and.r(x, y)), Nat.add(p, q))

def strict_and_l(x, y, p, q, lx, pq, hy, nl):
  match y:
    case Model.Lit{v}:
      match v:
        case False{}:
          absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
        case True{}:
          %add_one_r(Model.len(x)) : Le(_, Nat.add(p, q))
          le_add_mono(Model.len(x), 1n, p, q, lx, pq)
    case Model.Var{n}:
      %add_succ_right(Model.len(x), Model.len(Model.Var{n})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Var{n}), p, q, lx, hy({==}))
    case Model.Not{i}:
      %add_succ_right(Model.len(x), Model.len(Model.Not{i})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Not{i}), p, q, lx, hy({==}))
    case Model.And{l, r}:
      %add_succ_right(Model.len(x), Model.len(Model.And{l, r})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.And{l, r}), p, q, lx, hy({==}))
    case Model.Or{l, r}:
      %add_succ_right(Model.len(x), Model.len(Model.Or{l, r})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Or{l, r}), p, q, lx, hy({==}))

law strict_and:
  for +ol: Bool
  for +orr: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for lx: Le(Model.len(x), p)
  for ly: Le(Model.len(y), q)
  for pp: Le(1n, p)
  for pq: Le(1n, q)
  for sx: {ol == False{} : Bool} -> {is_lit(x) == False{} : Bool} -> Lt(Model.len(x), p)
  for sy: {orr == False{} : Bool} -> {is_lit(y) == False{} : Bool} -> Lt(Model.len(y), q)
  for no: {Bool.and(ol, orr) == False{} : Bool}
  for nl: {is_lit(red.and(x, y)) == False{} : Bool}
  Lt(Model.len(red.and(x, y)), Nat.add(p, q))

def strict_and(ol, orr, x, y, p, q, lx, ly, pp, pq, sx, sy, no, nl):
  match ol:
    case False{}:
      match x:
        case Model.Lit{v}:
          match v:
            case False{}:
              absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
            case True{}:
              le_add_mono(1n, Model.len(y), p, q, pp, ly)
        case Model.Var{n}:
          strict_and_r(Model.Var{n}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.Not{i}:
          strict_and_r(Model.Not{i}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.And{l, r}:
          strict_and_r(Model.And{l, r}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.Or{l, r}:
          strict_and_r(Model.Or{l, r}, y, p, q, sx({==}, {==}), ly, nl)
    case True{}:
      match x:
        case Model.Lit{v}:
          match v:
            case False{}:
              absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
            case True{}:
              le_trans(1n+Model.len(y), q, Nat.add(p, q), sy(no, nl), le_add_l(p, q))
        case Model.Var{n}:
          strict_and_l(Model.Var{n}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.Not{i}:
          strict_and_l(Model.Not{i}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.And{l, r}:
          strict_and_l(Model.And{l, r}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.Or{l, r}:
          strict_and_l(Model.Or{l, r}, y, p, q, lx, pq, ny => sy(no, ny), nl)

law eval_red_or_r:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  {Model.eval(red.or.r(a, b), env) == Bool.or(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_red_or_r(a, b, env):
  match b:
    case Model.Lit{v}:
      match v:
        case True{}:
          Equal.sym(Bool, Bool.or(Model.eval(a, env), True{}), True{}, bool_or_true(Model.eval(a, env)))
        case False{}:
          Equal.sym(Bool, Bool.or(Model.eval(a, env), False{}), Model.eval(a, env), bool_or_false(Model.eval(a, env)))
    case Model.Var{n}:
      {==}
    case Model.Not{i}:
      {==}
    case Model.And{l, r}:
      {==}
    case Model.Or{l, r}:
      {==}

law eval_red_or:
  for +a: Model.Expr
  for +b: Model.Expr
  for +env: Model.Env
  {Model.eval(red.or(a, b), env) == Bool.or(Model.eval(a, env), Model.eval(b, env)) : Bool}

def eval_red_or(a, b, env):
  match a:
    case Model.Lit{v}:
      match v:
        case True{}:
          {==}
        case False{}:
          {==}
    case Model.Var{n}:
      eval_red_or_r(Model.Var{n}, b, env)
    case Model.Not{i}:
      eval_red_or_r(Model.Not{i}, b, env)
    case Model.And{l, r}:
      eval_red_or_r(Model.And{l, r}, b, env)
    case Model.Or{l, r}:
      eval_red_or_r(Model.Or{l, r}, b, env)

law len_red_or_r:
  for +a: Model.Expr
  for +b: Model.Expr
  Le(Model.len(red.or.r(a, b)), Nat.add(Model.len(a), Model.len(b)))

def len_red_or_r(a, b):
  match b:
    case Model.Lit{v}:
      match v:
        case True{}:
          le_trans(1n, Model.len(a), Nat.add(Model.len(a), 1n), len_pos(a), le_add_r(Model.len(a), 1n))
        case False{}:
          le_add_r(Model.len(a), 1n)
    case Model.Var{n}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Var{n})))
    case Model.Not{i}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Not{i})))
    case Model.And{l, r}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.And{l, r})))
    case Model.Or{l, r}:
      le_refl(Nat.add(Model.len(a), Model.len(Model.Or{l, r})))

law len_red_or:
  for +a: Model.Expr
  for +b: Model.Expr
  Le(Model.len(red.or(a, b)), Nat.add(Model.len(a), Model.len(b)))

def len_red_or(a, b):
  match a:
    case Model.Lit{v}:
      match v:
        case True{}:
          le_zero(Model.len(b))
        case False{}:
          le_succ(Model.len(b))
    case Model.Var{n}:
      len_red_or_r(Model.Var{n}, b)
    case Model.Not{i}:
      len_red_or_r(Model.Not{i}, b)
    case Model.And{l, r}:
      len_red_or_r(Model.And{l, r}, b)
    case Model.Or{l, r}:
      len_red_or_r(Model.Or{l, r}, b)

law good_red_or_r:
  for +names: List<&2, String>
  for +a: Model.Expr
  for +b: Model.Expr
  for +na: {is_lit(a) == False{} : Bool}
  for +ga: {good(names, a) == True{} : Bool}
  for +gb: {good(names, b) == True{} : Bool}
  {good(names, red.or.r(a, b)) == True{} : Bool}

def good_red_or_r(names, a, b, na, ga, gb):
  match b:
    case Model.Lit{v}:
      match v:
        case True{}:
          {==}
        case False{}:
          ga
    case Model.Var{n}:
      and4(pure(a), over(names, a), pure(Model.Var{n}), over(names, Model.Var{n}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.Not{i}:
      and4(pure(a), over(names, a), pure(Model.Not{i}), over(names, Model.Not{i}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.And{l, r}:
      and4(pure(a), over(names, a), pure(Model.And{l, r}), over(names, Model.And{l, r}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)
    case Model.Or{l, r}:
      and4(pure(a), over(names, a), pure(Model.Or{l, r}), over(names, Model.Or{l, r}), or_false_r(is_lit(a), Bool.and(pure(a), over(names, a)), na, ga), gb)

law good_red_or:
  for +names: List<&2, String>
  for +a: Model.Expr
  for +b: Model.Expr
  for +ga: {good(names, a) == True{} : Bool}
  for +gb: {good(names, b) == True{} : Bool}
  {good(names, red.or(a, b)) == True{} : Bool}

def good_red_or(names, a, b, ga, gb):
  match a:
    case Model.Lit{v}:
      match v:
        case True{}:
          {==}
        case False{}:
          gb
    case Model.Var{n}:
      good_red_or_r(names, Model.Var{n}, b, {==}, ga, gb)
    case Model.Not{i}:
      good_red_or_r(names, Model.Not{i}, b, {==}, ga, gb)
    case Model.And{l, r}:
      good_red_or_r(names, Model.And{l, r}, b, {==}, ga, gb)
    case Model.Or{l, r}:
      good_red_or_r(names, Model.Or{l, r}, b, {==}, ga, gb)

law strict_or_r:
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for hx: Lt(Model.len(x), p)
  for ly: Le(Model.len(y), q)
  for nl: {is_lit(red.or.r(x, y)) == False{} : Bool}
  Lt(Model.len(red.or.r(x, y)), Nat.add(p, q))

def strict_or_r(x, y, p, q, hx, ly, nl):
  match y:
    case Model.Lit{v}:
      match v:
        case True{}:
          absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
        case False{}:
          le_trans(1n+Model.len(x), p, Nat.add(p, q), hx, le_add_r(p, q))
    case Model.Var{n}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Var{n}), p, q, hx, ly)
    case Model.Not{i}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Not{i}), p, q, hx, ly)
    case Model.And{l, r}:
      le_add_mono(1n+Model.len(x), Model.len(Model.And{l, r}), p, q, hx, ly)
    case Model.Or{l, r}:
      le_add_mono(1n+Model.len(x), Model.len(Model.Or{l, r}), p, q, hx, ly)

law strict_or_l:
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for lx: Le(Model.len(x), p)
  for pq: Le(1n, q)
  for hy: {is_lit(y) == False{} : Bool} -> Lt(Model.len(y), q)
  for nl: {is_lit(red.or.r(x, y)) == False{} : Bool}
  Lt(Model.len(red.or.r(x, y)), Nat.add(p, q))

def strict_or_l(x, y, p, q, lx, pq, hy, nl):
  match y:
    case Model.Lit{v}:
      match v:
        case True{}:
          absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
        case False{}:
          %add_one_r(Model.len(x)) : Le(_, Nat.add(p, q))
          le_add_mono(Model.len(x), 1n, p, q, lx, pq)
    case Model.Var{n}:
      %add_succ_right(Model.len(x), Model.len(Model.Var{n})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Var{n}), p, q, lx, hy({==}))
    case Model.Not{i}:
      %add_succ_right(Model.len(x), Model.len(Model.Not{i})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Not{i}), p, q, lx, hy({==}))
    case Model.And{l, r}:
      %add_succ_right(Model.len(x), Model.len(Model.And{l, r})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.And{l, r}), p, q, lx, hy({==}))
    case Model.Or{l, r}:
      %add_succ_right(Model.len(x), Model.len(Model.Or{l, r})) : Le(_, Nat.add(p, q))
      le_add_mono(Model.len(x), 1n+Model.len(Model.Or{l, r}), p, q, lx, hy({==}))

law strict_or:
  for +ol: Bool
  for +orr: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for +p: Nat
  for +q: Nat
  for lx: Le(Model.len(x), p)
  for ly: Le(Model.len(y), q)
  for pp: Le(1n, p)
  for pq: Le(1n, q)
  for sx: {ol == False{} : Bool} -> {is_lit(x) == False{} : Bool} -> Lt(Model.len(x), p)
  for sy: {orr == False{} : Bool} -> {is_lit(y) == False{} : Bool} -> Lt(Model.len(y), q)
  for no: {Bool.and(ol, orr) == False{} : Bool}
  for nl: {is_lit(red.or(x, y)) == False{} : Bool}
  Lt(Model.len(red.or(x, y)), Nat.add(p, q))

def strict_or(ol, orr, x, y, p, q, lx, ly, pp, pq, sx, sy, no, nl):
  match ol:
    case False{}:
      match x:
        case Model.Lit{v}:
          match v:
            case True{}:
              absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
            case False{}:
              le_add_mono(1n, Model.len(y), p, q, pp, ly)
        case Model.Var{n}:
          strict_or_r(Model.Var{n}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.Not{i}:
          strict_or_r(Model.Not{i}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.And{l, r}:
          strict_or_r(Model.And{l, r}, y, p, q, sx({==}, {==}), ly, nl)
        case Model.Or{l, r}:
          strict_or_r(Model.Or{l, r}, y, p, q, sx({==}, {==}), ly, nl)
    case True{}:
      match x:
        case Model.Lit{v}:
          match v:
            case True{}:
              absurd(Lt(1n, Nat.add(p, q)), true_clash(nl))
            case False{}:
              le_trans(1n+Model.len(y), q, Nat.add(p, q), sy(no, nl), le_add_l(p, q))
        case Model.Var{n}:
          strict_or_l(Model.Var{n}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.Not{i}:
          strict_or_l(Model.Not{i}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.And{l, r}:
          strict_or_l(Model.And{l, r}, y, p, q, lx, pq, ny => sy(no, ny), nl)
        case Model.Or{l, r}:
          strict_or_l(Model.Or{l, r}, y, p, q, lx, pq, ny => sy(no, ny), nl)

law red_eval:
  for +names: List<&2, String>
  for +e: Model.Expr
  for +env: Model.Env
  {Model.eval(red(names, e), env) == Model.eval(e, ext(names, env, Model.EnvNil{})) : Bool}

def red_eval(names, e, env):
  match e:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      Equal.trans(Bool, Model.eval(red.var(n, Optimizer.mem(n, names)), env), Bool.pick(Bool, Optimizer.mem(n, names), Model.lookup(env, n), False{}), Model.lookup(ext(names, env, Model.EnvNil{}), n), eval_red_var(n, Optimizer.mem(n, names), env), Equal.sym(Bool, Model.lookup(ext(names, env, Model.EnvNil{}), n), Bool.pick(Bool, Optimizer.mem(n, names), Model.lookup(env, n), False{}), lookup_ext(names, env, Model.EnvNil{}, n)))
    case Model.Not{i}:
      Equal.trans(Bool, Model.eval(red.not(red(names, i)), env), Bool.not(Model.eval(red(names, i), env)), Bool.not(Model.eval(i, ext(names, env, Model.EnvNil{}))), eval_red_not(red(names, i), env), not_cong(Model.eval(red(names, i), env), Model.eval(i, ext(names, env, Model.EnvNil{})), red_eval(names, i, env)))
    case Model.And{l, r}:
      Equal.trans(Bool, Model.eval(red.and(red(names, l), red(names, r)), env), Bool.and(Model.eval(red(names, l), env), Model.eval(red(names, r), env)), Bool.and(Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{}))), eval_red_and(red(names, l), red(names, r), env), and_cong(Model.eval(red(names, l), env), Model.eval(red(names, r), env), Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{})), red_eval(names, l, env), red_eval(names, r, env)))
    case Model.Or{l, r}:
      Equal.trans(Bool, Model.eval(red.or(red(names, l), red(names, r)), env), Bool.or(Model.eval(red(names, l), env), Model.eval(red(names, r), env)), Bool.or(Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{}))), eval_red_or(red(names, l), red(names, r), env), or_cong(Model.eval(red(names, l), env), Model.eval(red(names, r), env), Model.eval(l, ext(names, env, Model.EnvNil{})), Model.eval(r, ext(names, env, Model.EnvNil{})), red_eval(names, l, env), red_eval(names, r, env)))

law red_len:
  for +names: List<&2, String>
  for +e: Model.Expr
  Le(Model.len(red(names, e)), Model.len(e))

def red_len(names, e):
  match e:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      len_red_var(n, Optimizer.mem(n, names))
    case Model.Not{i}:
      le_trans(Model.len(red.not(red(names, i))), 1n+Model.len(red(names, i)), 1n+Model.len(i), len_red_not(red(names, i)), red_len(names, i))
    case Model.And{l, r}:
      le_trans(Model.len(red.and(red(names, l), red(names, r))), Nat.add(Model.len(red(names, l)), Model.len(red(names, r))), Nat.add(Model.len(l), Model.len(r)), len_red_and(red(names, l), red(names, r)), le_add_mono(Model.len(red(names, l)), Model.len(red(names, r)), Model.len(l), Model.len(r), red_len(names, l), red_len(names, r)))
    case Model.Or{l, r}:
      le_trans(Model.len(red.or(red(names, l), red(names, r))), Nat.add(Model.len(red(names, l)), Model.len(red(names, r))), Nat.add(Model.len(l), Model.len(r)), len_red_or(red(names, l), red(names, r)), le_add_mono(Model.len(red(names, l)), Model.len(red(names, r)), Model.len(l), Model.len(r), red_len(names, l), red_len(names, r)))

law red_good:
  for +names: List<&2, String>
  for +e: Model.Expr
  {good(names, red(names, e)) == True{} : Bool}

def red_good(names, e):
  match e:
    case Model.Lit{v}:
      {==}
    case Model.Var{n}:
      good_red_var(names, n, Optimizer.mem(n, names), {==})
    case Model.Not{i}:
      good_red_not(names, red(names, i), red_good(names, i))
    case Model.And{l, r}:
      good_red_and(names, red(names, l), red(names, r), red_good(names, l), red_good(names, r))
    case Model.Or{l, r}:
      good_red_or(names, red(names, l), red(names, r), red_good(names, l), red_good(names, r))

law red_strict:
  for +names: List<&2, String>
  for +e: Model.Expr
  for +no: {over(names, e) == False{} : Bool}
  for +nl: {is_lit(red(names, e)) == False{} : Bool}
  Lt(Model.len(red(names, e)), Model.len(e))

def red_strict(names, e, no, nl):
  match e:
    case Model.Lit{v}:
      absurd(Lt(1n, 1n), true_clash(no))
    case Model.Var{n}:
      strict_var(n, Optimizer.mem(n, names), no, nl)
    case Model.Not{i}:
      +eq = len_not_nl(red(names, i), nl)
      %Equal.sym(Nat, Model.len(red.not(red(names, i))), 1n+Model.len(red(names, i)), eq) : Lt(_, 1n+Model.len(i))
      red_strict(names, i, no, nl_not(red(names, i), nl))
    case Model.And{l, r}:
      strict_and(over(names, l), over(names, r), red(names, l), red(names, r), Model.len(l), Model.len(r), red_len(names, l), red_len(names, r), len_pos(l), len_pos(r), a => b => red_strict(names, l, a, b), a => b => red_strict(names, r, a, b), no, nl)
    case Model.Or{l, r}:
      strict_or(over(names, l), over(names, r), red(names, l), red(names, r), Model.len(l), Model.len(r), red_len(names, l), red_len(names, r), len_pos(l), len_pos(r), a => b => red_strict(names, l, a, b), a => b => red_strict(names, r, a, b), no, nl)

def eqe(a: Model.Expr, b: Model.Expr) -> Bool:
  match a b:
    case Model.Lit{x} Model.Lit{y}:
      Bool.not(Bool.xor(x, y))
    case Model.Var{x} Model.Var{y}:
      String.eq(x, y)
    case Model.Not{x} Model.Not{y}:
      eqe(x, y)
    case Model.And{al, ar} Model.And{bl, br}:
      Bool.and(eqe(al, bl), eqe(ar, br))
    case Model.Or{al, ar} Model.Or{bl, br}:
      Bool.and(eqe(al, bl), eqe(ar, br))
    case _ _:
      False{}

law eqe_refl:
  for +a: Model.Expr
  {eqe(a, a) == True{} : Bool}

def eqe_refl(a):
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
      eqe_refl(inner)
    case Model.And{l, r}:
      and_true(eqe(l, l), eqe(r, r), eqe_refl(l), eqe_refl(r))
    case Model.Or{l, r}:
      and_true(eqe(l, l), eqe(r, r), eqe_refl(l), eqe_refl(r))

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

law eqe_sound:
  for +a: Model.Expr
  for +b: Model.Expr
  for +e: {eqe(a, b) == True{} : Bool}
  {a == b : Model.Expr}

def eqe_sound(a, b, e):
  match a b:
    case Model.Lit{x} Model.Lit{y}:
      lit_sound(x, y, e)
    case Model.Var{x} Model.Var{y}:
      %string_eq_sound(x, y, e) : {Model.Var{x} == Model.Var{_} : Model.Expr}
      {==}
    case Model.Not{x} Model.Not{y}:
      %eqe_sound(x, y, e) : {Model.Not{x} == Model.Not{_} : Model.Expr}
      {==}
    case Model.And{al, ar} Model.And{bl, br}:
      %eqe_sound(al, bl, and_true_left(eqe(al, bl), eqe(ar, br), e)) : {Model.And{al, ar} == Model.And{_, br} : Model.Expr}
      %eqe_sound(ar, br, and_true_right(eqe(al, bl), eqe(ar, br), e)) : {Model.And{al, ar} == Model.And{al, _} : Model.Expr}
      {==}
    case Model.Or{al, ar} Model.Or{bl, br}:
      %eqe_sound(al, bl, and_true_left(eqe(al, bl), eqe(ar, br), e)) : {Model.Or{al, ar} == Model.Or{_, br} : Model.Expr}
      %eqe_sound(ar, br, and_true_right(eqe(al, bl), eqe(ar, br), e)) : {Model.Or{al, ar} == Model.Or{al, _} : Model.Expr}
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

def inb(+c: Model.Expr, xs: List<&2, Model.Expr>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(eqe(c, h), inb(c, t))

def nonehit(xs: List<&2, Model.Expr>, +names: List<&2, String>, +x: Model.Expr) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x))

def natq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      natq(p, q)

def ok(+names: List<&2, String>, +n: Nat, +c: Model.Expr) -> Bool:
  Bool.and(natq(Model.len(c), n), Bool.and(pure(c), over(names, c)))

def allok(xs: List<&2, Model.Expr>, +names: List<&2, String>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(ok(names, n, h), allok(t, names, n))

def target(split: Bool, i: Nat, s: Nat) -> Nat:
  match split:
    case False{}:
      s
    case True{}:
      Nat.add(i, s)

law natq_refl:
  for +n: Nat
  {natq(n, n) == True{} : Bool}

def natq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      natq_refl(p)

law natq_sound:
  for +a: Nat
  for +b: Nat
  for e: {natq(a, b) == True{} : Bool}
  {a == b : Nat}

def natq_sound(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      absurd({0n == 1n+q : Nat}, bool_clash(e))
    case 1n+p 0n:
      absurd({1n+p == 0n : Nat}, bool_clash(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, natq_sound(p, q, e))

law maybe_clash:
  for +x: Model.Expr
  for e: {Some{x} == None{} : Maybe<&2, Model.Expr>}
  Empty

def maybe_disc(m: Maybe<&2, Model.Expr>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def maybe_clash(x, e):
  %e : maybe_disc(_)
  Unit{}

def unwrap(+d: Model.Expr, m: Maybe<&2, Model.Expr>) -> Model.Expr:
  match m:
    case None{}:
      d
    case Some{x}:
      x

law some_inj:
  for +x: Model.Expr
  for +y: Model.Expr
  for e: {Some{x} == Some{y} : Maybe<&2, Model.Expr>}
  {x == y : Model.Expr}

def some_inj(x, y, e):
  Equal.cong(Maybe<&2, Model.Expr>, Model.Expr, m => unwrap(x, m), Some{x}, Some{y}, e)

law nonehit_step:
  for +b: Bool
  for +c: Model.Expr
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for eb: {eqe(c, h) == b : Bool}
  for hn: {Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)) == True{} : Bool}
  for hi: {Bool.or(b, inb(c, t)) == True{} : Bool}
  for ih: {inb(c, t) == True{} : Bool} -> {Optimizer.agree(names, Model.EnvNil{}, c, x) == False{} : Bool}
  {Optimizer.agree(names, Model.EnvNil{}, c, x) == False{} : Bool}

def nonehit_step(b, c, h, t, names, x, eb, hn, hi, ih):
  match b:
    case False{}:
      ih(hi)
    case True{}:
      %Equal.sym(Model.Expr, c, h, eqe_sound(c, h, eb)) : {Optimizer.agree(names, Model.EnvNil{}, _, x) == False{} : Bool}
      not_true(Optimizer.agree(names, Model.EnvNil{}, h, x), hn)

law nonehit_inb:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for +c: Model.Expr
  for +hn: {nonehit(xs, names, x) == True{} : Bool}
  for hi: {inb(c, xs) == True{} : Bool}
  {Optimizer.agree(names, Model.EnvNil{}, c, x) == False{} : Bool}

def nonehit_inb(xs, names, x, c, hn, hi):
  match xs:
    case Nil{}:
      absurd({Optimizer.agree(names, Model.EnvNil{}, c, x) == False{} : Bool}, bool_clash(hi))
    case +h <> +t:
      nonehit_step(eqe(c, h), c, h, t, names, x, {==}, and_true_left(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x), hn), hi, it => nonehit_inb(t, names, x, c, and_true_right(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x), hn), it))

law allok_step:
  for +b: Bool
  for +c: Model.Expr
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +n: Nat
  for eb: {eqe(c, h) == b : Bool}
  for ha: {ok(names, n, h) == True{} : Bool}
  for hi: {Bool.or(b, inb(c, t)) == True{} : Bool}
  for ih: {inb(c, t) == True{} : Bool} -> {ok(names, n, c) == True{} : Bool}
  {ok(names, n, c) == True{} : Bool}

def allok_step(b, c, h, t, names, n, eb, ha, hi, ih):
  match b:
    case False{}:
      ih(hi)
    case True{}:
      %Equal.sym(Model.Expr, c, h, eqe_sound(c, h, eb)) : {ok(names, n, _) == True{} : Bool}
      ha

law allok_inb:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +n: Nat
  for +c: Model.Expr
  for +ha: {allok(xs, names, n) == True{} : Bool}
  for hi: {inb(c, xs) == True{} : Bool}
  {ok(names, n, c) == True{} : Bool}

def allok_inb(xs, names, n, c, ha, hi):
  match xs:
    case Nil{}:
      absurd({ok(names, n, c) == True{} : Bool}, bool_clash(hi))
    case +h <> +t:
      allok_step(eqe(c, h), c, h, t, names, n, {==}, and_true_left(ok(names, n, h), allok(t, names, n), ha), hi, it => allok_inb(t, names, n, c, and_true_right(ok(names, n, h), allok(t, names, n), ha), it))

law inb_ecat_l:
  for +c: Model.Expr
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for h: {inb(c, a) == True{} : Bool}
  {inb(c, Optimizer.ecat(a, b)) == True{} : Bool}

def inb_ecat_l(c, a, b, h):
  match a:
    case Nil{}:
      absurd({inb(c, b) == True{} : Bool}, bool_clash(h))
    case +x <> +t:
      or_step(eqe(c, x), inb(c, t), inb(c, Optimizer.ecat(t, b)), h, e => inb_ecat_l(c, t, b, e))

law inb_ecat_r:
  for +c: Model.Expr
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for h: {inb(c, b) == True{} : Bool}
  {inb(c, Optimizer.ecat(a, b)) == True{} : Bool}

def inb_ecat_r(c, a, b, h):
  match a:
    case Nil{}:
      h
    case +x <> +t:
      or_true_right(eqe(c, x), inb(c, Optimizer.ecat(t, b)), inb_ecat_r(c, t, b, h))

law inb_nots:
  for +c: Model.Expr
  for +xs: List<&2, Model.Expr>
  for h: {inb(c, xs) == True{} : Bool}
  {inb(Model.Not{c}, Optimizer.nots(xs)) == True{} : Bool}

def inb_nots(c, xs, h):
  match xs:
    case Nil{}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case +x <> +t:
      or_step(eqe(c, x), inb(c, t), inb(Model.Not{c}, Optimizer.nots(t)), h, e => inb_nots(c, t, e))

law inb_leaves:
  for +n: String
  for +u: List<&2, String>
  for h: {Optimizer.mem(n, u) == True{} : Bool}
  {inb(Model.Var{n}, Optimizer.leaves(u)) == True{} : Bool}

def inb_leaves(n, u, h):
  match u:
    case Nil{}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case +x <> +t:
      or_step(String.eq(n, x), Optimizer.mem(n, t), inb(Model.Var{n}, Optimizer.leaves(t)), h, e => inb_leaves(n, t, e))

law or_step2:
  for +a: Bool
  for +c: Bool
  for +m: Bool
  for +n: Bool
  for ha: {a == True{} : Bool}
  for e: {Bool.or(c, m) == True{} : Bool}
  for ih: {m == True{} : Bool} -> {n == True{} : Bool}
  {Bool.or(Bool.and(a, c), n) == True{} : Bool}

def or_step2(a, c, m, n, ha, e, ih):
  match a:
    case False{}:
      absurd({n == True{} : Bool}, bool_clash(ha))
    case True{}:
      or_step(c, m, n, e, ih)

law inb_pairs:
  for +r: List<&2, Model.Expr>
  for +op: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for hy: {inb(y, r) == True{} : Bool}
  {inb(Optimizer.mk(op, x, y), Optimizer.pairs(op, x, r)) == True{} : Bool}

def inb_pairs(r, op, x, y, hy):
  match r:
    case Nil{}:
      absurd({inb(Optimizer.mk(op, x, y), Nil{}) == True{} : Bool}, bool_clash(hy))
    case +h <> +t:
      match op:
        case False{}:
          or_step2(eqe(x, x), eqe(y, h), inb(y, t), inb(Model.And{x, y}, Optimizer.pairs(False{}, x, t)), eqe_refl(x), hy, e => inb_pairs(t, False{}, x, y, e))
        case True{}:
          or_step2(eqe(x, x), eqe(y, h), inb(y, t), inb(Model.Or{x, y}, Optimizer.pairs(True{}, x, t)), eqe_refl(x), hy, e => inb_pairs(t, True{}, x, y, e))

law inb_prod_step:
  for +b: Bool
  for +op: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +r: List<&2, Model.Expr>
  for eb: {eqe(x, h) == b : Bool}
  for hx: {Bool.or(b, inb(x, t)) == True{} : Bool}
  for hy: {inb(y, r) == True{} : Bool}
  for ih: {inb(x, t) == True{} : Bool} -> {inb(Optimizer.mk(op, x, y), Optimizer.prod(op, t, r)) == True{} : Bool}
  {inb(Optimizer.mk(op, x, y), Optimizer.ecat(Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r))) == True{} : Bool}

def inb_prod_step(b, op, x, y, h, t, r, eb, hx, hy, ih):
  match b:
    case False{}:
      inb_ecat_r(Optimizer.mk(op, x, y), Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r), ih(hx))
    case True{}:
      %Equal.sym(Model.Expr, x, h, eqe_sound(x, h, eb)) : {inb(Optimizer.mk(op, _, y), Optimizer.ecat(Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r))) == True{} : Bool}
      inb_ecat_l(Optimizer.mk(op, h, y), Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r), inb_pairs(r, op, h, y, hy))

law inb_prod:
  for +l: List<&2, Model.Expr>
  for +op: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for +r: List<&2, Model.Expr>
  for hx: {inb(x, l) == True{} : Bool}
  for +hy: {inb(y, r) == True{} : Bool}
  {inb(Optimizer.mk(op, x, y), Optimizer.prod(op, l, r)) == True{} : Bool}

def inb_prod(l, op, x, y, r, hx, hy):
  match l:
    case Nil{}:
      absurd({False{} == True{} : Bool}, bool_clash(hx))
    case +h <> +t:
      inb_prod_step(eqe(x, h), op, x, y, h, t, r, {==}, hx, hy, e => inb_prod(t, op, x, y, r, e, hy))

law allok_ecat:
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +n: Nat
  for ha: {allok(a, names, n) == True{} : Bool}
  for hb: {allok(b, names, n) == True{} : Bool}
  {allok(Optimizer.ecat(a, b), names, n) == True{} : Bool}

def allok_ecat(a, b, names, n, ha, hb):
  match a:
    case Nil{}:
      hb
    case +h <> +t:
      +ha = ha
      and_true(ok(names, n, h), allok(Optimizer.ecat(t, b), names, n), and_true_left(ok(names, n, h), allok(t, names, n), ha), allok_ecat(t, b, names, n, and_true_right(ok(names, n, h), allok(t, names, n), ha), hb))

law allok_leaves:
  for +u: List<&2, String>
  for +names: List<&2, String>
  for +s: {subb(u, names) == True{} : Bool}
  {allok(Optimizer.leaves(u), names, 1n) == True{} : Bool}

def allok_leaves(u, names, s):
  match u:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(ok(names, 1n, Model.Var{h}), allok(Optimizer.leaves(t), names, 1n), and_true_left(Optimizer.mem(h, names), subb(t, names), s), allok_leaves(t, names, and_true_right(Optimizer.mem(h, names), subb(t, names), s)))

law allok_atoms:
  for +r: Nat
  for +names: List<&2, String>
  {allok(Optimizer.atoms(r, names), names, 1n+r) == True{} : Bool}

def allok_atoms(r, names):
  match r:
    case 0n:
      allok_leaves(names, names, subb_refl(names))
    case 1n+p:
      {==}

law allok_nots:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +n: Nat
  for +h: {allok(xs, names, n) == True{} : Bool}
  {allok(Optimizer.nots(xs), names, 1n+n) == True{} : Bool}

def allok_nots(xs, names, n, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      and_true(ok(names, 1n+n, Model.Not{x}), allok(Optimizer.nots(t), names, 1n+n), and_true_left(ok(names, n, x), allok(t, names, n), h), allok_nots(t, names, n, and_true_right(ok(names, n, x), allok(t, names, n), h)))

law natq_add:
  for +x: Model.Expr
  for +y: Model.Expr
  for +i: Nat
  for +j: Nat
  for ex: {Model.len(x) == i : Nat}
  for ey: {Model.len(y) == j : Nat}
  {natq(Nat.add(Model.len(x), Model.len(y)), Nat.add(i, j)) == True{} : Bool}

def natq_add(x, y, i, j, ex, ey):
  %Equal.sym(Nat, Model.len(x), i, ex) : {natq(Nat.add(_, Model.len(y)), Nat.add(i, j)) == True{} : Bool}
  %Equal.sym(Nat, Model.len(y), j, ey) : {natq(Nat.add(i, _), Nat.add(i, j)) == True{} : Bool}
  natq_refl(Nat.add(i, j))

law ok_mk:
  for +op: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  for +names: List<&2, String>
  for +i: Nat
  for +j: Nat
  for +hx: {ok(names, i, x) == True{} : Bool}
  for +hy: {ok(names, j, y) == True{} : Bool}
  {ok(names, Nat.add(i, j), Optimizer.mk(op, x, y)) == True{} : Bool}

def ok_mk(op, x, y, names, i, j, hx, hy):
  match op:
    case False{}:
      and_true(natq(Nat.add(Model.len(x), Model.len(y)), Nat.add(i, j)), Bool.and(Bool.and(pure(x), pure(y)), Bool.and(over(names, x), over(names, y))), natq_add(x, y, i, j, natq_sound(Model.len(x), i, and_true_left(natq(Model.len(x), i), Bool.and(pure(x), over(names, x)), hx)), natq_sound(Model.len(y), j, and_true_left(natq(Model.len(y), j), Bool.and(pure(y), over(names, y)), hy))), and4(pure(x), over(names, x), pure(y), over(names, y), and_true_right(natq(Model.len(x), i), Bool.and(pure(x), over(names, x)), hx), and_true_right(natq(Model.len(y), j), Bool.and(pure(y), over(names, y)), hy)))
    case True{}:
      and_true(natq(Nat.add(Model.len(x), Model.len(y)), Nat.add(i, j)), Bool.and(Bool.and(pure(x), pure(y)), Bool.and(over(names, x), over(names, y))), natq_add(x, y, i, j, natq_sound(Model.len(x), i, and_true_left(natq(Model.len(x), i), Bool.and(pure(x), over(names, x)), hx)), natq_sound(Model.len(y), j, and_true_left(natq(Model.len(y), j), Bool.and(pure(y), over(names, y)), hy))), and4(pure(x), over(names, x), pure(y), over(names, y), and_true_right(natq(Model.len(x), i), Bool.and(pure(x), over(names, x)), hx), and_true_right(natq(Model.len(y), j), Bool.and(pure(y), over(names, y)), hy)))

law allok_pairs:
  for +r: List<&2, Model.Expr>
  for +op: Bool
  for +x: Model.Expr
  for +names: List<&2, String>
  for +i: Nat
  for +j: Nat
  for +hx: {ok(names, i, x) == True{} : Bool}
  for +hr: {allok(r, names, j) == True{} : Bool}
  {allok(Optimizer.pairs(op, x, r), names, Nat.add(i, j)) == True{} : Bool}

def allok_pairs(r, op, x, names, i, j, hx, hr):
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(ok(names, Nat.add(i, j), Optimizer.mk(op, x, h)), allok(Optimizer.pairs(op, x, t), names, Nat.add(i, j)), ok_mk(op, x, h, names, i, j, hx, and_true_left(ok(names, j, h), allok(t, names, j), hr)), allok_pairs(t, op, x, names, i, j, hx, and_true_right(ok(names, j, h), allok(t, names, j), hr)))

law allok_prod:
  for +l: List<&2, Model.Expr>
  for +op: Bool
  for +r: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +i: Nat
  for +j: Nat
  for +hl: {allok(l, names, i) == True{} : Bool}
  for +hr: {allok(r, names, j) == True{} : Bool}
  {allok(Optimizer.prod(op, l, r), names, Nat.add(i, j)) == True{} : Bool}

def allok_prod(l, op, r, names, i, j, hl, hr):
  match l:
    case Nil{}:
      {==}
    case +h <> +t:
      allok_ecat(Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r), names, Nat.add(i, j), allok_pairs(r, op, h, names, i, j, and_true_left(ok(names, i, h), allok(t, names, i), hl), hr), allok_prod(t, op, r, names, i, j, and_true_right(ok(names, i, h), allok(t, names, i), hl), hr))

law allok_cast:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +a: Nat
  for +b: Nat
  for e: {a == b : Nat}
  for h: {allok(xs, names, a) == True{} : Bool}
  {allok(xs, names, b) == True{} : Bool}

def allok_cast(xs, names, a, b, e, h):
  %e : {allok(xs, names, _) == True{} : Bool}
  h

law cands_sound:
  for +g: Nat
  for +s: Nat
  for +split: Bool
  for +i: Nat
  for +names: List<&2, String>
  {allok(Optimizer.cands(g, s, split, i, names), names, target(split, i, s)) == True{} : Bool}

def cands_sound(g, s, split, i, names):
  match g:
    case 0n:
      {==}
    case 1n+h:
      match s:
        case 0n:
          {==}
        case 1n+r:
          match split:
            case False{}:
              allok_ecat(Optimizer.atoms(r, names), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, names)), Optimizer.cands(1n+h, r, True{}, 1n, names)), names, 1n+r, allok_atoms(r, names), allok_ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, names)), Optimizer.cands(1n+h, r, True{}, 1n, names), names, 1n+r, allok_nots(Optimizer.cands(h, r, False{}, 0n, names), names, r, cands_sound(h, r, False{}, 0n, names)), cands_sound(1n+h, r, True{}, 1n, names)))
            case True{}:
              allok_ecat(Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+r, False{}, 0n, names)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+r, False{}, 0n, names)), Optimizer.cands(1n+h, r, True{}, 1n+i, names)), names, Nat.add(i, 1n+r), allok_prod(Optimizer.cands(h, i, False{}, 0n, names), False{}, Optimizer.cands(h, 1n+r, False{}, 0n, names), names, i, 1n+r, cands_sound(h, i, False{}, 0n, names), cands_sound(h, 1n+r, False{}, 0n, names)), allok_ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+r, False{}, 0n, names)), Optimizer.cands(1n+h, r, True{}, 1n+i, names), names, Nat.add(i, 1n+r), allok_prod(Optimizer.cands(h, i, False{}, 0n, names), True{}, Optimizer.cands(h, 1n+r, False{}, 0n, names), names, i, 1n+r, cands_sound(h, i, False{}, 0n, names), cands_sound(h, 1n+r, False{}, 0n, names)), allok_cast(Optimizer.cands(1n+h, r, True{}, 1n+i, names), names, 1n+Nat.add(i, r), Nat.add(i, 1n+r), Equal.sym(Nat, Nat.add(i, 1n+r), 1n+Nat.add(i, r), add_succ_right(i, r)), cands_sound(1n+h, r, True{}, 1n+i, names))))

law inb_cast:
  for +c: Model.Expr
  for +h: Nat
  for +names: List<&2, String>
  for +a: Nat
  for +b: Nat
  for e: {a == b : Nat}
  for hi: {inb(c, Optimizer.cands(h, a, False{}, 0n, names)) == True{} : Bool}
  {inb(c, Optimizer.cands(h, b, False{}, 0n, names)) == True{} : Bool}

def inb_cast(c, h, names, a, b, e, hi):
  %e : {inb(c, Optimizer.cands(h, _, False{}, 0n, names)) == True{} : Bool}
  hi

law add_r_one:
  for +d: Nat
  {add_r(d, 1n) == 1n+d : Nat}

def add_r_one(d):
  %add_r_zero(d) : {add_r(d, 1n) == 1n+_ : Nat}
  add_r_succ(d, 0n)

law split_mem:
  for +d: Nat
  for +i: Nat
  for +op: Bool
  for +a: Model.Expr
  for +b: Model.Expr
  for +lb: Nat
  for +h: Nat
  for +names: List<&2, String>
  for ina: {inb(a, Optimizer.cands(h, add_r(d, i), False{}, 0n, names)) == True{} : Bool}
  for inb_b: {inb(b, Optimizer.cands(h, lb, False{}, 0n, names)) == True{} : Bool}
  {inb(Optimizer.mk(op, a, b), Optimizer.cands(1n+h, Nat.add(d, lb), True{}, i, names)) == True{} : Bool}

def split_mem(d, i, op, a, b, lb, h, names, ina, inb_b):
  match d:
    case 0n:
      match op:
        case False{}:
          match lb:
            case 0n:
              match h:
                case 0n:
                  absurd({False{} == True{} : Bool}, bool_clash(inb_b))
                case 1n+q:
                  absurd({False{} == True{} : Bool}, bool_clash(inb_b))
            case 1n+rb:
              inb_ecat_l(Model.And{a, b}, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+rb, False{}, 0n, names)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+rb, False{}, 0n, names)), Optimizer.cands(1n+h, rb, True{}, 1n+i, names)), inb_prod(Optimizer.cands(h, i, False{}, 0n, names), False{}, a, b, Optimizer.cands(h, 1n+rb, False{}, 0n, names), ina, inb_b))
        case True{}:
          match lb:
            case 0n:
              match h:
                case 0n:
                  absurd({False{} == True{} : Bool}, bool_clash(inb_b))
                case 1n+q:
                  absurd({False{} == True{} : Bool}, bool_clash(inb_b))
            case 1n+rb:
              inb_ecat_r(Model.Or{a, b}, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+rb, False{}, 0n, names)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+rb, False{}, 0n, names)), Optimizer.cands(1n+h, rb, True{}, 1n+i, names)), inb_ecat_l(Model.Or{a, b}, Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+rb, False{}, 0n, names)), Optimizer.cands(1n+h, rb, True{}, 1n+i, names), inb_prod(Optimizer.cands(h, i, False{}, 0n, names), True{}, a, b, Optimizer.cands(h, 1n+rb, False{}, 0n, names), ina, inb_b)))
    case 1n+e:
      inb_ecat_r(Optimizer.mk(op, a, b), Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+Nat.add(e, lb), False{}, 0n, names)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+Nat.add(e, lb), False{}, 0n, names)), Optimizer.cands(1n+h, Nat.add(e, lb), True{}, 1n+i, names)), inb_ecat_r(Optimizer.mk(op, a, b), Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, names), Optimizer.cands(h, 1n+Nat.add(e, lb), False{}, 0n, names)), Optimizer.cands(1n+h, Nat.add(e, lb), True{}, 1n+i, names), split_mem(e, 1n+i, op, a, b, lb, h, names, ina, inb_b)))

law bin_mem:
  for +la: Nat
  for +lb: Nat
  for +h: Nat
  for +op: Bool
  for +a: Model.Expr
  for +b: Model.Expr
  for +names: List<&2, String>
  for ina: {inb(a, Optimizer.cands(h, la, False{}, 0n, names)) == True{} : Bool}
  for inb_b: {inb(b, Optimizer.cands(h, lb, False{}, 0n, names)) == True{} : Bool}
  {inb(Optimizer.mk(op, a, b), Optimizer.cands(1n+h, Nat.add(la, lb), False{}, 0n, names)) == True{} : Bool}

def bin_mem(la, lb, h, op, a, b, names, ina, inb_b):
  match la:
    case 0n:
      match h:
        case 0n:
          absurd({inb(Optimizer.mk(op, a, b), Optimizer.cands(1n, lb, False{}, 0n, names)) == True{} : Bool}, bool_clash(ina))
        case 1n+q:
          absurd({inb(Optimizer.mk(op, a, b), Optimizer.cands(1n+1n+q, lb, False{}, 0n, names)) == True{} : Bool}, bool_clash(ina))
    case 1n+pa:
      inb_ecat_r(Optimizer.mk(op, a, b), Optimizer.atoms(Nat.add(pa, lb), names), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, Nat.add(pa, lb), False{}, 0n, names)), Optimizer.cands(1n+h, Nat.add(pa, lb), True{}, 1n, names)), inb_ecat_r(Optimizer.mk(op, a, b), Optimizer.nots(Optimizer.cands(h, Nat.add(pa, lb), False{}, 0n, names)), Optimizer.cands(1n+h, Nat.add(pa, lb), True{}, 1n, names), split_mem(pa, 1n, op, a, b, lb, h, names, inb_cast(a, h, names, 1n+pa, add_r(pa, 1n), Equal.sym(Nat, add_r(pa, 1n), 1n+pa, add_r_one(pa)), ina), inb_b)))

law le_part_l_aux:
  for +la: Nat
  for +lb: Nat
  for pb: Le(1n, lb)
  Le(1n+la, Nat.add(la, lb))

def le_part_l_aux(la, lb, pb):
  %add_one_r(la) : Le(_, Nat.add(la, lb))
  le_add_mono(la, 1n, la, lb, le_refl(la), pb)

law le_part_l:
  for +la: Nat
  for +lb: Nat
  for +h: Nat
  for hle: Le(Nat.add(la, lb), 1n+h)
  for pb: Le(1n, lb)
  Le(la, h)

def le_part_l(la, lb, h, hle, pb):
  le_trans(1n+la, Nat.add(la, lb), 1n+h, le_part_l_aux(la, lb, pb), hle)

law le_part_r:
  for +la: Nat
  for +lb: Nat
  for +h: Nat
  for hle: Le(Nat.add(la, lb), 1n+h)
  for pa: Le(1n, la)
  Le(lb, h)

def le_part_r(la, lb, h, hle, pa):
  le_trans(1n+lb, Nat.add(la, lb), 1n+h, le_add_mono(1n, lb, la, lb, pa, le_refl(lb)), hle)

law comp:
  for +c: Model.Expr
  for +g: Nat
  for +names: List<&2, String>
  for +hle: Le(Model.len(c), g)
  for +hp: {pure(c) == True{} : Bool}
  for +ho: {over(names, c) == True{} : Bool}
  {inb(c, Optimizer.cands(g, Model.len(c), False{}, 0n, names)) == True{} : Bool}

def comp(c, g, names, hle, hp, ho):
  match c:
    case Model.Lit{v}:
      absurd({inb(Model.Lit{v}, Optimizer.cands(g, 1n, False{}, 0n, names)) == True{} : Bool}, bool_clash(hp))
    case Model.Var{n}:
      match g:
        case 0n:
          absurd({False{} == True{} : Bool}, bool_clash(hle))
        case 1n+h:
          inb_ecat_l(Model.Var{n}, Optimizer.leaves(names), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, 0n, False{}, 0n, names)), Optimizer.cands(1n+h, 0n, True{}, 1n, names)), inb_leaves(n, names, ho))
    case Model.Not{a}:
      match g:
        case 0n:
          absurd({False{} == True{} : Bool}, bool_clash(hle))
        case 1n+h:
          inb_ecat_r(Model.Not{a}, Optimizer.atoms(Model.len(a), names), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, Model.len(a), False{}, 0n, names)), Optimizer.cands(1n+h, Model.len(a), True{}, 1n, names)), inb_ecat_l(Model.Not{a}, Optimizer.nots(Optimizer.cands(h, Model.len(a), False{}, 0n, names)), Optimizer.cands(1n+h, Model.len(a), True{}, 1n, names), inb_nots(a, Optimizer.cands(h, Model.len(a), False{}, 0n, names), comp(a, h, names, hle, hp, ho))))
    case Model.And{a, b}:
      match g:
        case 0n:
          absurd({False{} == True{} : Bool}, bool_clash(le_trans(1n, Model.len(Model.And{a, b}), 0n, len_pos(Model.And{a, b}), hle)))
        case 1n+h:
          bin_mem(Model.len(a), Model.len(b), h, False{}, a, b, names, comp(a, h, names, le_part_l(Model.len(a), Model.len(b), h, hle, len_pos(b)), and_true_left(pure(a), pure(b), hp), and_true_left(over(names, a), over(names, b), ho)), comp(b, h, names, le_part_r(Model.len(a), Model.len(b), h, hle, len_pos(a)), and_true_right(pure(a), pure(b), hp), and_true_right(over(names, a), over(names, b), ho)))
    case Model.Or{a, b}:
      match g:
        case 0n:
          absurd({False{} == True{} : Bool}, bool_clash(le_trans(1n, Model.len(Model.Or{a, b}), 0n, len_pos(Model.Or{a, b}), hle)))
        case 1n+h:
          bin_mem(Model.len(a), Model.len(b), h, True{}, a, b, names, comp(a, h, names, le_part_l(Model.len(a), Model.len(b), h, hle, len_pos(b)), and_true_left(pure(a), pure(b), hp), and_true_left(over(names, a), over(names, b), ho)), comp(b, h, names, le_part_r(Model.len(a), Model.len(b), h, hle, len_pos(a)), and_true_right(pure(a), pure(b), hp), and_true_right(over(names, a), over(names, b), ho)))

law find_none_step:
  for +hit: Bool
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for eh: {Optimizer.agree(names, Model.EnvNil{}, h, x) == hit : Bool}
  for e: {Optimizer.find.if(h, u => Optimizer.find(t, names, x), hit) == None{} : Maybe<&2, Model.Expr>}
  for ih: {Optimizer.find(t, names, x) == None{} : Maybe<&2, Model.Expr>} -> {nonehit(t, names, x) == True{} : Bool}
  {Bool.and(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x)) == True{} : Bool}

def find_none_step(hit, h, t, names, x, eh, e, ih):
  match hit:
    case False{}:
      and_true(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x), not_cong(Optimizer.agree(names, Model.EnvNil{}, h, x), False{}, eh), ih(e))
    case True{}:
      absurd({Bool.and(Bool.not(Optimizer.agree(names, Model.EnvNil{}, h, x)), nonehit(t, names, x)) == True{} : Bool}, maybe_clash(h, e))

law find_none:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for e: {Optimizer.find(xs, names, x) == None{} : Maybe<&2, Model.Expr>}
  {nonehit(xs, names, x) == True{} : Bool}

def find_none(xs, names, x, e):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      find_none_step(Optimizer.agree(names, Model.EnvNil{}, h, x), h, t, names, x, {==}, e, et => find_none(t, names, x, et))

law find_in_step:
  for +hit: Bool
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for +r: Model.Expr
  for e: {Optimizer.find.if(h, u => Optimizer.find(t, names, x), hit) == Some{r} : Maybe<&2, Model.Expr>}
  for ih: {Optimizer.find(t, names, x) == Some{r} : Maybe<&2, Model.Expr>} -> {inb(r, t) == True{} : Bool}
  {Bool.or(eqe(r, h), inb(r, t)) == True{} : Bool}

def find_in_step(hit, h, t, names, x, r, e, ih):
  match hit:
    case False{}:
      or_true_right(eqe(r, h), inb(r, t), ih(e))
    case True{}:
      %some_inj(h, r, e) : {Bool.or(eqe(_, h), inb(_, t)) == True{} : Bool}
      or_true_left(eqe(h, h), inb(h, t), eqe_refl(h))

law find_in:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for +r: Model.Expr
  for e: {Optimizer.find(xs, names, x) == Some{r} : Maybe<&2, Model.Expr>}
  {inb(r, xs) == True{} : Bool}

def find_in(xs, names, x, r, e):
  match xs:
    case Nil{}:
      absurd({False{} == True{} : Bool}, maybe_clash(r, Equal.sym(Maybe<&2, Model.Expr>, None{}, Some{r}, e)))
    case +h <> +t:
      find_in_step(Optimizer.agree(names, Model.EnvNil{}, h, x), h, t, names, x, r, e, et => find_in(t, names, x, r, et))

law find_agree_step:
  for +hit: Bool
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for +r: Model.Expr
  for eh: {Optimizer.agree(names, Model.EnvNil{}, h, x) == hit : Bool}
  for e: {Optimizer.find.if(h, u => Optimizer.find(t, names, x), hit) == Some{r} : Maybe<&2, Model.Expr>}
  for ih: {Optimizer.find(t, names, x) == Some{r} : Maybe<&2, Model.Expr>} -> {Optimizer.agree(names, Model.EnvNil{}, r, x) == True{} : Bool}
  {Optimizer.agree(names, Model.EnvNil{}, r, x) == True{} : Bool}

def find_agree_step(hit, h, t, names, x, r, eh, e, ih):
  match hit:
    case False{}:
      ih(e)
    case True{}:
      %some_inj(h, r, e) : {Optimizer.agree(names, Model.EnvNil{}, _, x) == True{} : Bool}
      eh

law find_agree:
  for +xs: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +x: Model.Expr
  for +r: Model.Expr
  for e: {Optimizer.find(xs, names, x) == Some{r} : Maybe<&2, Model.Expr>}
  {Optimizer.agree(names, Model.EnvNil{}, r, x) == True{} : Bool}

def find_agree(xs, names, x, r, e):
  match xs:
    case Nil{}:
      absurd({Optimizer.agree(names, Model.EnvNil{}, r, x) == True{} : Bool}, maybe_clash(r, Equal.sym(Maybe<&2, Model.Expr>, None{}, Some{r}, e)))
    case +h <> +t:
      find_agree_step(Optimizer.agree(names, Model.EnvNil{}, h, x), h, t, names, x, r, {==}, e, et => find_agree(t, names, x, r, et))

def below(+n: Nat, +names: List<&2, String>, +x: Model.Expr) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(below(j, names, x), nonehit(Optimizer.level(j, names), names, x))

law level_inb:
  for +c: Model.Expr
  for +j: Nat
  for +names: List<&2, String>
  for +hp: {pure(c) == True{} : Bool}
  for +ho: {over(names, c) == True{} : Bool}
  for eq: {Model.len(c) == j : Nat}
  {inb(c, Optimizer.level(j, names)) == True{} : Bool}

def level_inb(c, j, names, hp, ho, eq):
  %eq : {inb(c, Optimizer.cands(_, _, False{}, 0n, names)) == True{} : Bool}
  comp(c, Model.len(c), names, le_refl(Model.len(c)), hp, ho)

law agree_clash:
  for +names: List<&2, String>
  for +c: Model.Expr
  for +x: Model.Expr
  for t: {Optimizer.agree(names, Model.EnvNil{}, c, x) == True{} : Bool}
  for f: {Optimizer.agree(names, Model.EnvNil{}, c, x) == False{} : Bool}
  Empty

def agree_clash(names, c, x, t, f):
  true_clash(Equal.trans(Bool, True{}, Optimizer.agree(names, Model.EnvNil{}, c, x), False{}, Equal.sym(Bool, Optimizer.agree(names, Model.EnvNil{}, c, x), True{}, t), f))

law below_use:
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for +c: Model.Expr
  for +hb: {below(n, names, x) == True{} : Bool}
  for +hp: {pure(c) == True{} : Bool}
  for +ho: {over(names, c) == True{} : Bool}
  for +hag: {Optimizer.agree(names, Model.EnvNil{}, c, x) == True{} : Bool}
  for hlt: Lt(Model.len(c), n)
  Empty

def below_use(n, names, x, c, hb, hp, ho, hag, hlt):
  match n:
    case 0n:
      bool_clash(hlt)
    case 1n+j:
      le_cases(Empty, Model.len(c), j, hlt, lt => below_use(j, names, x, c, and_true_left(below(j, names, x), nonehit(Optimizer.level(j, names), names, x), hb), hp, ho, hag, lt), eq => agree_clash(names, c, x, hag, nonehit_inb(Optimizer.level(j, names), names, x, c, and_true_right(below(j, names, x), nonehit(Optimizer.level(j, names), names, x), hb), level_inb(c, j, names, hp, ho, eq))))

law level_ok:
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for +r: Model.Expr
  for e: {Optimizer.find(Optimizer.level(n, names), names, x) == Some{r} : Maybe<&2, Model.Expr>}
  {ok(names, n, r) == True{} : Bool}

def level_ok(n, names, x, r, e):
  allok_inb(Optimizer.level(n, names), names, n, r, cands_sound(n, n, False{}, 0n, names), find_in(Optimizer.level(n, names), names, x, r, e))

law ok_over:
  for +names: List<&2, String>
  for +n: Nat
  for +r: Model.Expr
  for +h: {ok(names, n, r) == True{} : Bool}
  {over(names, r) == True{} : Bool}

def ok_over(names, n, r, h):
  and_true_right(pure(r), over(names, r), and_true_right(natq(Model.len(r), n), Bool.and(pure(r), over(names, r)), h))

law ok_pure:
  for +names: List<&2, String>
  for +n: Nat
  for +r: Model.Expr
  for +h: {ok(names, n, r) == True{} : Bool}
  {pure(r) == True{} : Bool}

def ok_pure(names, n, r, h):
  and_true_left(pure(r), over(names, r), and_true_right(natq(Model.len(r), n), Bool.and(pure(r), over(names, r)), h))

law ok_len:
  for +names: List<&2, String>
  for +n: Nat
  for +r: Model.Expr
  for +h: {ok(names, n, r) == True{} : Bool}
  {Model.len(r) == n : Nat}

def ok_len(names, n, r, h):
  natq_sound(Model.len(r), n, and_true_left(natq(Model.len(r), n), Bool.and(pure(r), over(names, r)), h))

law search_over_step:
  for +m: Maybe<&2, Model.Expr>
  for +f: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for em: {Optimizer.find(Optimizer.level(n, names), names, x) == m : Maybe<&2, Model.Expr>}
  for ih: {over(names, Optimizer.search(f, 1n+n, names, x)) == True{} : Bool}
  {over(names, Optimizer.search.if(u => Optimizer.search(f, 1n+n, names, x), m)) == True{} : Bool}

def search_over_step(m, f, n, names, x, em, ih):
  match m:
    case None{}:
      ih
    case Some{r}:
      ok_over(names, n, r, level_ok(n, names, x, r, em))

law search_over:
  for +f: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for +ox: {over(names, x) == True{} : Bool}
  {over(names, Optimizer.search(f, n, names, x)) == True{} : Bool}

def search_over(f, n, names, x, ox):
  match f:
    case 0n:
      ox
    case 1n+g:
      search_over_step(Optimizer.find(Optimizer.level(n, names), names, x), g, n, names, x, {==}, search_over(g, 1n+n, names, x, ox))

law agree_refl:
  for +names: List<&2, String>
  for +x: Model.Expr
  {Optimizer.agree(names, Model.EnvNil{}, x, x) == True{} : Bool}

def agree_refl(names, x):
  agree_by(names, Model.EnvNil{}, x, x, +w => {==})

law search_agree_step:
  for +m: Maybe<&2, Model.Expr>
  for +f: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for em: {Optimizer.find(Optimizer.level(n, names), names, x) == m : Maybe<&2, Model.Expr>}
  for ih: {Optimizer.agree(names, Model.EnvNil{}, Optimizer.search(f, 1n+n, names, x), x) == True{} : Bool}
  {Optimizer.agree(names, Model.EnvNil{}, Optimizer.search.if(u => Optimizer.search(f, 1n+n, names, x), m), x) == True{} : Bool}

def search_agree_step(m, f, n, names, x, em, ih):
  match m:
    case None{}:
      ih
    case Some{r}:
      find_agree(Optimizer.level(n, names), names, x, r, em)

law search_agree:
  for +f: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  {Optimizer.agree(names, Model.EnvNil{}, Optimizer.search(f, n, names, x), x) == True{} : Bool}

def search_agree(f, n, names, x):
  match f:
    case 0n:
      agree_refl(names, x)
    case 1n+g:
      search_agree_step(Optimizer.find(Optimizer.level(n, names), names, x), g, n, names, x, {==}, search_agree(g, 1n+n, names, x))

law search_len_step:
  for +m: Maybe<&2, Model.Expr>
  for +g: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for +c: Model.Expr
  for em: {Optimizer.find(Optimizer.level(n, names), names, x) == m : Maybe<&2, Model.Expr>}
  for +hb: {below(n, names, x) == True{} : Bool}
  for +hp: {pure(c) == True{} : Bool}
  for +ho: {over(names, c) == True{} : Bool}
  for +hag: {Optimizer.agree(names, Model.EnvNil{}, c, x) == True{} : Bool}
  for ih: {below(1n+n, names, x) == True{} : Bool} -> Le(Model.len(Optimizer.search(g, 1n+n, names, x)), Model.len(c))
  Le(Model.len(Optimizer.search.if(u => Optimizer.search(g, 1n+n, names, x), m)), Model.len(c))

def search_len_step(m, g, n, names, x, c, em, hb, hp, ho, hag, ih):
  match m:
    case None{}:
      ih(and_true(below(n, names, x), nonehit(Optimizer.level(n, names), names, x), hb, find_none(Optimizer.level(n, names), names, x, em)))
    case Some{r}:
      %Equal.sym(Nat, Model.len(r), n, ok_len(names, n, r, level_ok(n, names, x, r, em))) : Le(_, Model.len(c))
      not_lt_le(Model.len(c), n, lt => below_use(n, names, x, c, hb, hp, ho, hag, lt))

law search_len:
  for +f: Nat
  for +n: Nat
  for +names: List<&2, String>
  for +x: Model.Expr
  for +c: Model.Expr
  for +hb: {below(n, names, x) == True{} : Bool}
  for +hp: {pure(c) == True{} : Bool}
  for +ho: {over(names, c) == True{} : Bool}
  for +hag: {Optimizer.agree(names, Model.EnvNil{}, c, x) == True{} : Bool}
  for +d: Model.Expr
  for +hpd: {pure(d) == True{} : Bool}
  for +hod: {over(names, d) == True{} : Bool}
  for +hagd: {Optimizer.agree(names, Model.EnvNil{}, d, x) == True{} : Bool}
  for +hld: Lt(Model.len(d), add_r(f, n))
  Le(Model.len(Optimizer.search(f, n, names, x)), Model.len(c))

def search_len(f, n, names, x, c, hb, hp, ho, hag, d, hpd, hod, hagd, hld):
  match f:
    case 0n:
      absurd(Le(Model.len(x), Model.len(c)), below_use(n, names, x, d, hb, hpd, hod, hagd, hld))
    case 1n+g:
      search_len_step(Optimizer.find(Optimizer.level(n, names), names, x), g, n, names, x, c, {==}, hb, hp, ho, hag, hb2 => search_len(g, 1n+n, names, x, c, hb2, hp, ho, hag, d, hpd, hod, hagd, hld))

law lit_inb:
  for +y: Model.Expr
  for h: {is_lit(y) == True{} : Bool}
  {inb(y, Optimizer.lits()) == True{} : Bool}

def lit_inb(y, h):
  match y:
    case Model.Lit{v}:
      match v:
        case False{}:
          {==}
        case True{}:
          {==}
    case Model.Var{n}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case Model.Not{i}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case Model.And{l, r}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case Model.Or{l, r}:
      absurd({False{} == True{} : Bool}, bool_clash(h))

law not_lit_step:
  for +b: Bool
  for +names: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for eb: {is_lit(y) == b : Bool}
  for hn: {nonehit(Optimizer.lits(), names, x) == True{} : Bool}
  for hag: {Optimizer.agree(names, Model.EnvNil{}, y, x) == True{} : Bool}
  {b == False{} : Bool}

def not_lit_step(b, names, x, y, eb, hn, hag):
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, agree_clash(names, y, x, hag, nonehit_inb(Optimizer.lits(), names, x, y, hn, lit_inb(y, eb))))

law not_lit:
  for +names: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for hn: {nonehit(Optimizer.lits(), names, x) == True{} : Bool}
  for hag: {Optimizer.agree(names, Model.EnvNil{}, y, x) == True{} : Bool}
  {is_lit(y) == False{} : Bool}

def not_lit(names, x, y, hn, hag):
  not_lit_step(is_lit(y), names, x, y, {==}, hn, hag)

def litok(+names: List<&2, String>, +r: Model.Expr) -> Bool:
  Bool.and(natq(Model.len(r), 1n), over(names, r))

law litok_t:
  for +b: Bool
  for +names: List<&2, String>
  for +r: Model.Expr
  for eb: {eqe(r, Model.Lit{True{}}) == b : Bool}
  for hi: {Bool.or(b, False{}) == True{} : Bool}
  {litok(names, r) == True{} : Bool}

def litok_t(b, names, r, eb, hi):
  match b:
    case False{}:
      absurd({litok(names, r) == True{} : Bool}, bool_clash(hi))
    case True{}:
      %Equal.sym(Model.Expr, r, Model.Lit{True{}}, eqe_sound(r, Model.Lit{True{}}, eb)) : {litok(names, _) == True{} : Bool}
      {==}

law litok_f:
  for +b: Bool
  for +names: List<&2, String>
  for +r: Model.Expr
  for eb: {eqe(r, Model.Lit{False{}}) == b : Bool}
  for hi: {Bool.or(b, Bool.or(eqe(r, Model.Lit{True{}}), False{})) == True{} : Bool}
  {litok(names, r) == True{} : Bool}

def litok_f(b, names, r, eb, hi):
  match b:
    case False{}:
      litok_t(eqe(r, Model.Lit{True{}}), names, r, {==}, hi)
    case True{}:
      %Equal.sym(Model.Expr, r, Model.Lit{False{}}, eqe_sound(r, Model.Lit{False{}}, eb)) : {litok(names, _) == True{} : Bool}
      {==}

law lits_litok:
  for +names: List<&2, String>
  for +r: Model.Expr
  for hi: {inb(r, Optimizer.lits()) == True{} : Bool}
  {litok(names, r) == True{} : Bool}

def lits_litok(names, r, hi):
  litok_f(eqe(r, Model.Lit{False{}}), names, r, {==}, hi)

law opt_over_step:
  for +m: Maybe<&2, Model.Expr>
  for +x: Model.Expr
  for +names: List<&2, String>
  for em: {Optimizer.find(Optimizer.lits(), names, x) == m : Maybe<&2, Model.Expr>}
  for +ox: {over(names, x) == True{} : Bool}
  {over(names, Optimizer.search.if(u => Optimizer.search(Model.len(x), 1n, names, x), m)) == True{} : Bool}

def opt_over_step(m, x, names, em, ox):
  match m:
    case None{}:
      search_over(Model.len(x), 1n, names, x, ox)
    case Some{r}:
      and_true_right(natq(Model.len(r), 1n), over(names, r), lits_litok(names, r, find_in(Optimizer.lits(), names, x, r, em)))

law opt_over:
  for +x: Model.Expr
  {over(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.optimize(x)) == True{} : Bool}

def opt_over(x):
  opt_over_step(Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x), x, Optimizer.uniq(Optimizer.vars(x), Nil{}), {==}, over_vars(x))

law opt_agree_step:
  for +m: Maybe<&2, Model.Expr>
  for +x: Model.Expr
  for +names: List<&2, String>
  for em: {Optimizer.find(Optimizer.lits(), names, x) == m : Maybe<&2, Model.Expr>}
  {Optimizer.agree(names, Model.EnvNil{}, Optimizer.search.if(u => Optimizer.search(Model.len(x), 1n, names, x), m), x) == True{} : Bool}

def opt_agree_step(m, x, names, em):
  match m:
    case None{}:
      search_agree(Model.len(x), 1n, names, x)
    case Some{r}:
      find_agree(Optimizer.lits(), names, x, r, em)

law opt_agree:
  for +x: Model.Expr
  {Optimizer.agree(Optimizer.uniq(Optimizer.vars(x), Nil{}), Model.EnvNil{}, Optimizer.optimize(x), x) == True{} : Bool}

def opt_agree(x):
  opt_agree_step(Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x), x, Optimizer.uniq(Optimizer.vars(x), Nil{}), {==})

law red_agree:
  for +names: List<&2, String>
  for +x: Model.Expr
  for +ox: {over(names, x) == True{} : Bool}
  {Optimizer.agree(names, Model.EnvNil{}, red(names, x), x) == True{} : Bool}

def red_agree(names, x, ox):
  agree_by(names, Model.EnvNil{}, red(names, x), x, +w => Equal.trans(Bool, Model.eval(red(names, x), w), Model.eval(x, ext(names, w, Model.EnvNil{})), Model.eval(x, w), red_eval(names, x, w), eval_ext(names, w, x, ox)))

law witness_len:
  for +names: List<&2, String>
  for +x: Model.Expr
  Lt(Model.len(red(names, x)), add_r(Model.len(x), 1n))

def witness_len(names, x):
  %Equal.sym(Nat, add_r(Model.len(x), 1n), 1n+Model.len(x), add_r_one(Model.len(x))) : Lt(Model.len(red(names, x)), _)
  red_len(names, x)

law opt_len_none:
  for +x: Model.Expr
  for +names: List<&2, String>
  for +other: Model.Expr
  for +hn: {nonehit(Optimizer.lits(), names, x) == True{} : Bool}
  for +ox: {over(names, x) == True{} : Bool}
  for q: Laws.Equivalent(other, x)
  Le(Model.len(Optimizer.search(Model.len(x), 1n, names, x)), Model.len(other))

def opt_len_none(x, names, other, hn, ox, q):
  +agc = agree_by(names, Model.EnvNil{}, red(names, other), x, +w => Equal.trans(Bool, Model.eval(red(names, other), w), Model.eval(other, ext(names, w, Model.EnvNil{})), Model.eval(x, w), red_eval(names, other, w), Equal.trans(Bool, Model.eval(other, ext(names, w, Model.EnvNil{})), Model.eval(x, ext(names, w, Model.EnvNil{})), Model.eval(x, w), q(ext(names, w, Model.EnvNil{})), eval_ext(names, w, x, ox))))
  +nlc = not_lit(names, x, red(names, other), hn, agc)
  +agd = red_agree(names, x, ox)
  +nld = not_lit(names, x, red(names, x), hn, agd)
  le_trans(Model.len(Optimizer.search(Model.len(x), 1n, names, x)), Model.len(red(names, other)), Model.len(other), search_len(Model.len(x), 1n, names, x, red(names, other), {==}, good_pure(names, red(names, other), red_good(names, other), nlc), good_over(names, red(names, other), red_good(names, other), nlc), agc, red(names, x), good_pure(names, red(names, x), red_good(names, x), nld), good_over(names, red(names, x), red_good(names, x), nld), agd, witness_len(names, x)), red_len(names, other))

law opt_len_step:
  for +m: Maybe<&2, Model.Expr>
  for +x: Model.Expr
  for +names: List<&2, String>
  for +other: Model.Expr
  for em: {Optimizer.find(Optimizer.lits(), names, x) == m : Maybe<&2, Model.Expr>}
  for +ox: {over(names, x) == True{} : Bool}
  for q: Laws.Equivalent(other, x)
  Le(Model.len(Optimizer.search.if(u => Optimizer.search(Model.len(x), 1n, names, x), m)), Model.len(other))

def opt_len_step(m, x, names, other, em, ox, q):
  match m:
    case None{}:
      opt_len_none(x, names, other, find_none(Optimizer.lits(), names, x, em), ox, q)
    case Some{r}:
      %Equal.sym(Nat, Model.len(r), 1n, natq_sound(Model.len(r), 1n, and_true_left(natq(Model.len(r), 1n), over(names, r), lits_litok(names, r, find_in(Optimizer.lits(), names, x, r, em))))) : Le(_, Model.len(other))
      len_pos(other)

law opt_len:
  for +x: Model.Expr
  for +other: Model.Expr
  for q: Laws.Equivalent(other, x)
  Le(Model.len(Optimizer.optimize(x)), Model.len(other))

def opt_len(x, other, q):
  opt_len_step(Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x), x, Optimizer.uniq(Optimizer.vars(x), Nil{}), other, {==}, over_vars(x), q)

law pick_tf:
  for +b: Bool
  for h: {Bool.pick(Bool, b, True{}, False{}) == True{} : Bool}
  {b == True{} : Bool}

def pick_tf(b, h):
  match b:
    case False{}:
      absurd({False{} == True{} : Bool}, bool_clash(h))
    case True{}:
      {==}

law self_bound:
  for +n: String
  {True{} == Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n) : Bool}

def self_bound(n):
  Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, True{}, False{}), True{}, String.eq(n, n), Equal.sym(Bool, String.eq(n, n), True{}, string_eq_refl(n)))

law leaf_lit:
  for +names: List<&2, String>
  for +r: Model.Expr
  for +b: Bool
  for hl: Le(Model.len(r), 1n)
  for +ho: {over(names, r) == True{} : Bool}
  for +hag: {Optimizer.agree(names, Model.EnvNil{}, r, Model.Lit{b}) == True{} : Bool}
  {r == Model.Lit{b} : Model.Expr}

def leaf_lit(names, r, b, hl, ho, hag):
  match r:
    case Model.Lit{v}:
      Equal.cong(Bool, Model.Expr, z => Model.Lit{z}, v, b, agree_eval(names, Model.Lit{v}, Model.Lit{b}, {==}, {==}, hag, Model.EnvNil{}))
    case Model.Var{+n}:
      absurd({Model.Var{n} == Model.Lit{b} : Model.Expr}, true_clash(Equal.trans(Bool, True{}, b, False{}, Equal.trans(Bool, True{}, Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n), b, self_bound(n), agree_eval(names, Model.Var{n}, Model.Lit{b}, ho, {==}, hag, Model.EnvCons{n, True{}, Model.EnvNil{}})), Equal.sym(Bool, False{}, b, agree_eval(names, Model.Var{n}, Model.Lit{b}, ho, {==}, hag, Model.EnvNil{})))))
    case Model.Not{i}:
      absurd({Model.Not{i} == Model.Lit{b} : Model.Expr}, bool_clash(le_trans(1n, Model.len(i), 0n, len_pos(i), hl)))
    case Model.And{l, r}:
      absurd({Model.And{l, r} == Model.Lit{b} : Model.Expr}, bool_clash(le_trans(2n, Nat.add(Model.len(l), Model.len(r)), 1n, le_add_mono(1n, 1n, Model.len(l), Model.len(r), len_pos(l), len_pos(r)), hl)))
    case Model.Or{l, r}:
      absurd({Model.Or{l, r} == Model.Lit{b} : Model.Expr}, bool_clash(le_trans(2n, Nat.add(Model.len(l), Model.len(r)), 1n, le_add_mono(1n, 1n, Model.len(l), Model.len(r), len_pos(l), len_pos(r)), hl)))

law leaf_var:
  for +names: List<&2, String>
  for +r: Model.Expr
  for +n: String
  for hl: Le(Model.len(r), 1n)
  for +ho: {over(names, r) == True{} : Bool}
  for +hon: {over(names, Model.Var{n}) == True{} : Bool}
  for +hag: {Optimizer.agree(names, Model.EnvNil{}, r, Model.Var{n}) == True{} : Bool}
  {r == Model.Var{n} : Model.Expr}

def leaf_var(names, r, n, hl, ho, hon, hag):
  match r:
    case Model.Lit{v}:
      absurd({Model.Lit{v} == Model.Var{n} : Model.Expr}, bool_clash(Equal.trans(Bool, False{}, v, True{}, Equal.sym(Bool, v, False{}, agree_eval(names, Model.Lit{v}, Model.Var{n}, {==}, hon, hag, Model.EnvNil{})), Equal.trans(Bool, v, Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n), True{}, agree_eval(names, Model.Lit{v}, Model.Var{n}, {==}, hon, hag, Model.EnvCons{n, True{}, Model.EnvNil{}}), Equal.sym(Bool, True{}, Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n), self_bound(n))))))
    case Model.Var{+m}:
      Equal.cong(String, Model.Expr, z => Model.Var{z}, m, n, string_eq_sound(m, n, pick_tf(String.eq(m, n), Equal.trans(Bool, Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, m), Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n), True{}, agree_eval(names, Model.Var{m}, Model.Var{n}, ho, hon, hag, Model.EnvCons{n, True{}, Model.EnvNil{}}), Equal.sym(Bool, True{}, Model.lookup(Model.EnvCons{n, True{}, Model.EnvNil{}}, n), self_bound(n))))))
    case Model.Not{i}:
      absurd({Model.Not{i} == Model.Var{n} : Model.Expr}, bool_clash(le_trans(1n, Model.len(i), 0n, len_pos(i), hl)))
    case Model.And{l, r}:
      absurd({Model.And{l, r} == Model.Var{n} : Model.Expr}, bool_clash(le_trans(2n, Nat.add(Model.len(l), Model.len(r)), 1n, le_add_mono(1n, 1n, Model.len(l), Model.len(r), len_pos(l), len_pos(r)), hl)))
    case Model.Or{l, r}:
      absurd({Model.Or{l, r} == Model.Var{n} : Model.Expr}, bool_clash(le_trans(2n, Nat.add(Model.len(l), Model.len(r)), 1n, le_add_mono(1n, 1n, Model.len(l), Model.len(r), len_pos(l), len_pos(r)), hl)))

law const_result:
  for +x: Model.Expr
  for +b: Bool
  for +h: {Optimizer.agree(Optimizer.uniq(Optimizer.vars(x), Nil{}), Model.EnvNil{}, Model.Lit{b}, x) == True{} : Bool}
  {Optimizer.optimize(x) == Model.Lit{b} : Model.Expr}

def const_result(x, b, h):
  leaf_lit(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.optimize(x), b, opt_len(x, Model.Lit{b}, +w => agree_eval(Optimizer.uniq(Optimizer.vars(x), Nil{}), Model.Lit{b}, x, {==}, over_vars(x), h, w)), opt_over(x), agree_by(Optimizer.uniq(Optimizer.vars(x), Nil{}), Model.EnvNil{}, Optimizer.optimize(x), Model.Lit{b}, +w => Equal.trans(Bool, Model.eval(Optimizer.optimize(x), w), Model.eval(x, w), b, agree_eval(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.optimize(x), x, opt_over(x), over_vars(x), opt_agree(x), w), Equal.sym(Bool, b, Model.eval(x, w), agree_eval(Optimizer.uniq(Optimizer.vars(x), Nil{}), Model.Lit{b}, x, {==}, over_vars(x), h, w)))))

def Laws.preserves_meaning(expr, env):
  agree_eval(Optimizer.uniq(Optimizer.vars(expr), Nil{}), Optimizer.optimize(expr), expr, opt_over(expr), over_vars(expr), opt_agree(expr), env)

def Laws.optimal(expr):
  (+w => agree_eval(Optimizer.uniq(Optimizer.vars(expr), Nil{}), Optimizer.optimize(expr), expr, opt_over(expr), over_vars(expr), opt_agree(expr), w), +other => q => opt_len(expr, other, q))

def Laws.keeps_variables(name):
  leaf_var(Optimizer.uniq(Optimizer.vars(Model.Var{name}), Nil{}), Optimizer.optimize(Model.Var{name}), name, opt_len(Model.Var{name}, Model.Var{name}, +w => {==}), opt_over(Model.Var{name}), over_vars(Model.Var{name}), opt_agree(Model.Var{name}))

def Laws.keeps_literals(value):
  leaf_lit(Optimizer.uniq(Optimizer.vars(Model.Lit{value}), Nil{}), Optimizer.optimize(Model.Lit{value}), value, opt_len(Model.Lit{value}, Model.Lit{value}, +w => {==}), opt_over(Model.Lit{value}), opt_agree(Model.Lit{value}))

def filtE.put(+h: Model.Expr, r: List<&2, Model.Expr>, keep: Bool) -> List<&2, Model.Expr>:
  match keep:
    case False{}:
      r
    case True{}:
      h <> r

def filtE(+names: List<&2, String>, xs: List<&2, Model.Expr>) -> List<&2, Model.Expr>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      filtE.put(h, filtE(names, t), over(names, h))

def allh1(xs: List<&2, Model.Expr>, +v: List<&2, String>, +w: List<&2, String>, +y: Model.Expr) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, h, y)), over(v, h)), allh1(t, v, w, y))

def allh2(xs: List<&2, Model.Expr>, +v: List<&2, String>, +w: List<&2, String>, +x: Model.Expr, +y: Model.Expr) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.or(Bool.not(over(v, h)), Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, h, y), Optimizer.agree(v, Model.EnvNil{}, h, x)))), allh2(t, v, w, x, y))

law ecat_cong:
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for +c: List<&2, Model.Expr>
  for +d: List<&2, Model.Expr>
  for ac: {a == c : List<&2, Model.Expr>}
  for bd: {b == d : List<&2, Model.Expr>}
  {Optimizer.ecat(a, b) == Optimizer.ecat(c, d) : List<&2, Model.Expr>}

def ecat_cong(a, b, c, d, ac, bd):
  %ac : {Optimizer.ecat(a, b) == Optimizer.ecat(_, d) : List<&2, Model.Expr>}
  %bd : {Optimizer.ecat(a, b) == Optimizer.ecat(a, _) : List<&2, Model.Expr>}
  {==}

law pute_cat:
  for +h: Model.Expr
  for +x: List<&2, Model.Expr>
  for +y: List<&2, Model.Expr>
  for +z: List<&2, Model.Expr>
  for +k: Bool
  for ih: {x == Optimizer.ecat(y, z) : List<&2, Model.Expr>}
  {filtE.put(h, x, k) == Optimizer.ecat(filtE.put(h, y, k), z) : List<&2, Model.Expr>}

def pute_cat(h, x, y, z, k, ih):
  match k:
    case False{}:
      ih
    case True{}:
      Equal.cong(List<&2, Model.Expr>, List<&2, Model.Expr>, q => h <> q, x, Optimizer.ecat(y, z), ih)

law filtE_ecat:
  for +names: List<&2, String>
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  {filtE(names, Optimizer.ecat(a, b)) == Optimizer.ecat(filtE(names, a), filtE(names, b)) : List<&2, Model.Expr>}

def filtE_ecat(names, a, b):
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      pute_cat(h, filtE(names, Optimizer.ecat(t, b)), filtE(names, t), filtE(names, b), over(names, h), filtE_ecat(names, t, b))

law pute_nots:
  for +h: Model.Expr
  for +x: List<&2, Model.Expr>
  for +y: List<&2, Model.Expr>
  for +k: Bool
  for ih: {x == Optimizer.nots(y) : List<&2, Model.Expr>}
  {filtE.put(Model.Not{h}, x, k) == Optimizer.nots(filtE.put(h, y, k)) : List<&2, Model.Expr>}

def pute_nots(h, x, y, k, ih):
  match k:
    case False{}:
      ih
    case True{}:
      Equal.cong(List<&2, Model.Expr>, List<&2, Model.Expr>, q => Model.Not{h} <> q, x, Optimizer.nots(y), ih)

law filtE_nots:
  for +names: List<&2, String>
  for +xs: List<&2, Model.Expr>
  {filtE(names, Optimizer.nots(xs)) == Optimizer.nots(filtE(names, xs)) : List<&2, Model.Expr>}

def filtE_nots(names, xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      pute_nots(h, filtE(names, Optimizer.nots(t)), filtE(names, t), over(names, h), filtE_nots(names, t))

law pute_leaves:
  for +h: String
  for +x: List<&2, Model.Expr>
  for +y: List<&2, String>
  for +k: Bool
  for ih: {x == Optimizer.leaves(y) : List<&2, Model.Expr>}
  {filtE.put(Model.Var{h}, x, k) == Optimizer.leaves(filtS.put(h, y, k)) : List<&2, Model.Expr>}

def pute_leaves(h, x, y, k, ih):
  match k:
    case False{}:
      ih
    case True{}:
      Equal.cong(List<&2, Model.Expr>, List<&2, Model.Expr>, q => Model.Var{h} <> q, x, Optimizer.leaves(y), ih)

law filtE_leaves:
  for +names: List<&2, String>
  for +u: List<&2, String>
  {filtE(names, Optimizer.leaves(u)) == Optimizer.leaves(filtS(names, u)) : List<&2, Model.Expr>}

def filtE_leaves(names, u):
  match u:
    case Nil{}:
      {==}
    case +h <> +t:
      pute_leaves(h, filtE(names, Optimizer.leaves(t)), filtS(names, t), Optimizer.mem(h, names), filtE_leaves(names, t))

law over_mk:
  for +names: List<&2, String>
  for +op: Bool
  for +x: Model.Expr
  for +y: Model.Expr
  {over(names, Optimizer.mk(op, x, y)) == Bool.and(over(names, x), over(names, y)) : Bool}

def over_mk(names, op, x, y):
  match op:
    case False{}:
      {==}
    case True{}:
      {==}

law pute_pairs:
  for +op: Bool
  for +x: Model.Expr
  for +h: Model.Expr
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for +k: Bool
  for ih: {a == Optimizer.pairs(op, x, b) : List<&2, Model.Expr>}
  {filtE.put(Optimizer.mk(op, x, h), a, k) == Optimizer.pairs(op, x, filtE.put(h, b, k)) : List<&2, Model.Expr>}

def pute_pairs(op, x, h, a, b, k, ih):
  match k:
    case False{}:
      ih
    case True{}:
      Equal.cong(List<&2, Model.Expr>, List<&2, Model.Expr>, q => Optimizer.mk(op, x, h) <> q, a, Optimizer.pairs(op, x, b), ih)

law pairs_t:
  for +r: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +op: Bool
  for +x: Model.Expr
  for +ox: {over(names, x) == True{} : Bool}
  {filtE(names, Optimizer.pairs(op, x, r)) == Optimizer.pairs(op, x, filtE(names, r)) : List<&2, Model.Expr>}

def pairs_t(r, names, op, x, ox):
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      +e = Equal.trans(Bool, over(names, Optimizer.mk(op, x, h)), Bool.and(over(names, x), over(names, h)), over(names, h), over_mk(names, op, x, h), Equal.cong(Bool, Bool, z => Bool.and(z, over(names, h)), over(names, x), True{}, ox))
      %Equal.sym(Bool, over(names, Optimizer.mk(op, x, h)), over(names, h), e) : {filtE.put(Optimizer.mk(op, x, h), filtE(names, Optimizer.pairs(op, x, t)), _) == Optimizer.pairs(op, x, filtE.put(h, filtE(names, t), over(names, h))) : List<&2, Model.Expr>}
      pute_pairs(op, x, h, filtE(names, Optimizer.pairs(op, x, t)), filtE(names, t), over(names, h), pairs_t(t, names, op, x, ox))

law pairs_f:
  for +r: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +op: Bool
  for +x: Model.Expr
  for +ox: {over(names, x) == False{} : Bool}
  {filtE(names, Optimizer.pairs(op, x, r)) == Nil{} : List<&2, Model.Expr>}

def pairs_f(r, names, op, x, ox):
  match r:
    case Nil{}:
      {==}
    case +h <> +t:
      +e = Equal.trans(Bool, over(names, Optimizer.mk(op, x, h)), Bool.and(over(names, x), over(names, h)), False{}, over_mk(names, op, x, h), Equal.cong(Bool, Bool, z => Bool.and(z, over(names, h)), over(names, x), False{}, ox))
      %Equal.sym(Bool, over(names, Optimizer.mk(op, x, h)), False{}, e) : {filtE.put(Optimizer.mk(op, x, h), filtE(names, Optimizer.pairs(op, x, t)), _) == Nil{} : List<&2, Model.Expr>}
      pairs_f(t, names, op, x, ox)

law prod_step:
  for +k: Bool
  for +names: List<&2, String>
  for +op: Bool
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +r: List<&2, Model.Expr>
  for +ek: {over(names, h) == k : Bool}
  for ih: {filtE(names, Optimizer.prod(op, t, r)) == Optimizer.prod(op, filtE(names, t), filtE(names, r)) : List<&2, Model.Expr>}
  {Optimizer.ecat(filtE(names, Optimizer.pairs(op, h, r)), filtE(names, Optimizer.prod(op, t, r))) == Optimizer.prod(op, filtE.put(h, filtE(names, t), k), filtE(names, r)) : List<&2, Model.Expr>}

def prod_step(k, names, op, h, t, r, ek, ih):
  match k:
    case False{}:
      %Equal.sym(List<&2, Model.Expr>, filtE(names, Optimizer.pairs(op, h, r)), Nil{}, pairs_f(r, names, op, h, ek)) : {Optimizer.ecat(_, filtE(names, Optimizer.prod(op, t, r))) == Optimizer.prod(op, filtE(names, t), filtE(names, r)) : List<&2, Model.Expr>}
      ih
    case True{}:
      ecat_cong(filtE(names, Optimizer.pairs(op, h, r)), filtE(names, Optimizer.prod(op, t, r)), Optimizer.pairs(op, h, filtE(names, r)), Optimizer.prod(op, filtE(names, t), filtE(names, r)), pairs_t(r, names, op, h, ek), ih)

law filtE_prod:
  for +l: List<&2, Model.Expr>
  for +names: List<&2, String>
  for +op: Bool
  for +r: List<&2, Model.Expr>
  {filtE(names, Optimizer.prod(op, l, r)) == Optimizer.prod(op, filtE(names, l), filtE(names, r)) : List<&2, Model.Expr>}

def filtE_prod(l, names, op, r):
  match l:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, Model.Expr>, filtE(names, Optimizer.ecat(Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r))), Optimizer.ecat(filtE(names, Optimizer.pairs(op, h, r)), filtE(names, Optimizer.prod(op, t, r))), Optimizer.prod(op, filtE.put(h, filtE(names, t), over(names, h)), filtE(names, r)), filtE_ecat(names, Optimizer.pairs(op, h, r), Optimizer.prod(op, t, r)), prod_step(over(names, h), names, op, h, t, r, {==}, filtE_prod(t, names, op, r)))

law prod_cong:
  for +op: Bool
  for +a: List<&2, Model.Expr>
  for +b: List<&2, Model.Expr>
  for +c: List<&2, Model.Expr>
  for +d: List<&2, Model.Expr>
  for ac: {a == c : List<&2, Model.Expr>}
  for bd: {b == d : List<&2, Model.Expr>}
  {Optimizer.prod(op, a, b) == Optimizer.prod(op, c, d) : List<&2, Model.Expr>}

def prod_cong(op, a, b, c, d, ac, bd):
  %ac : {Optimizer.prod(op, a, b) == Optimizer.prod(op, _, d) : List<&2, Model.Expr>}
  %bd : {Optimizer.prod(op, a, b) == Optimizer.prod(op, a, _) : List<&2, Model.Expr>}
  {==}

law atoms_eq:
  for +r: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +filt: {filtS(v, w) == v : List<&2, String>}
  {filtE(v, Optimizer.atoms(r, w)) == Optimizer.atoms(r, v) : List<&2, Model.Expr>}

def atoms_eq(r, v, w, filt):
  match r:
    case 0n:
      Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.leaves(w)), Optimizer.leaves(filtS(v, w)), Optimizer.leaves(v), filtE_leaves(v, w), Equal.cong(List<&2, String>, List<&2, Model.Expr>, z => Optimizer.leaves(z), filtS(v, w), v, filt))
    case 1n+p:
      {==}

law filtE_cands:
  for +g: Nat
  for +s: Nat
  for +split: Bool
  for +i: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +filt: {filtS(v, w) == v : List<&2, String>}
  {filtE(v, Optimizer.cands(g, s, split, i, w)) == Optimizer.cands(g, s, split, i, v) : List<&2, Model.Expr>}

def filtE_cands(g, s, split, i, v, w, filt):
  match g:
    case 0n:
      {==}
    case 1n+h:
      match s:
        case 0n:
          {==}
        case 1n+r:
          match split:
            case False{}:
              Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.ecat(Optimizer.atoms(r, w), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w)))), Optimizer.ecat(filtE(v, Optimizer.atoms(r, w)), filtE(v, Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w)))), Optimizer.ecat(Optimizer.atoms(r, v), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n, v))), filtE_ecat(v, Optimizer.atoms(r, w), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w))), ecat_cong(filtE(v, Optimizer.atoms(r, w)), filtE(v, Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w))), Optimizer.atoms(r, v), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n, v)), atoms_eq(r, v, w, filt), Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w))), Optimizer.ecat(filtE(v, Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w))), filtE(v, Optimizer.cands(1n+h, r, True{}, 1n, w))), Optimizer.ecat(Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n, v)), filtE_ecat(v, Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n, w)), ecat_cong(filtE(v, Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w))), filtE(v, Optimizer.cands(1n+h, r, True{}, 1n, w)), Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n, v), Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, w))), Optimizer.nots(filtE(v, Optimizer.cands(h, r, False{}, 0n, w))), Optimizer.nots(Optimizer.cands(h, r, False{}, 0n, v)), filtE_nots(v, Optimizer.cands(h, r, False{}, 0n, w)), Equal.cong(List<&2, Model.Expr>, List<&2, Model.Expr>, z => Optimizer.nots(z), filtE(v, Optimizer.cands(h, r, False{}, 0n, w)), Optimizer.cands(h, r, False{}, 0n, v), filtE_cands(h, r, False{}, 0n, v, w, filt))), filtE_cands(1n+h, r, True{}, 1n, v, w, filt)))))
            case True{}:
              Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.ecat(Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w)))), Optimizer.ecat(filtE(v, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), filtE(v, Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w)))), Optimizer.ecat(Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n+i, v))), filtE_ecat(v, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w))), ecat_cong(filtE(v, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), filtE(v, Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w))), Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n+i, v)), Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), Optimizer.prod(False{}, filtE(v, Optimizer.cands(h, i, False{}, 0n, w)), filtE(v, Optimizer.cands(h, 1n+r, False{}, 0n, w))), Optimizer.prod(False{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), filtE_prod(Optimizer.cands(h, i, False{}, 0n, w), v, False{}, Optimizer.cands(h, 1n+r, False{}, 0n, w)), prod_cong(False{}, filtE(v, Optimizer.cands(h, i, False{}, 0n, w)), filtE(v, Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v), filtE_cands(h, i, False{}, 0n, v, w, filt), filtE_cands(h, 1n+r, False{}, 0n, v, w, filt))), Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w))), Optimizer.ecat(filtE(v, Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), filtE(v, Optimizer.cands(1n+h, r, True{}, 1n+i, w))), Optimizer.ecat(Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n+i, v)), filtE_ecat(v, Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(1n+h, r, True{}, 1n+i, w)), ecat_cong(filtE(v, Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), filtE(v, Optimizer.cands(1n+h, r, True{}, 1n+i, w)), Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), Optimizer.cands(1n+h, r, True{}, 1n+i, v), Equal.trans(List<&2, Model.Expr>, filtE(v, Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, w), Optimizer.cands(h, 1n+r, False{}, 0n, w))), Optimizer.prod(True{}, filtE(v, Optimizer.cands(h, i, False{}, 0n, w)), filtE(v, Optimizer.cands(h, 1n+r, False{}, 0n, w))), Optimizer.prod(True{}, Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v)), filtE_prod(Optimizer.cands(h, i, False{}, 0n, w), v, True{}, Optimizer.cands(h, 1n+r, False{}, 0n, w)), prod_cong(True{}, filtE(v, Optimizer.cands(h, i, False{}, 0n, w)), filtE(v, Optimizer.cands(h, 1n+r, False{}, 0n, w)), Optimizer.cands(h, i, False{}, 0n, v), Optimizer.cands(h, 1n+r, False{}, 0n, v), filtE_cands(h, i, False{}, 0n, v, w, filt), filtE_cands(h, 1n+r, False{}, 0n, v, w, filt))), filtE_cands(1n+h, r, True{}, 1n+i, v, w, filt)))))

law ff_step:
  for +o: Bool
  for +aw: Bool
  for +av: Bool
  for +h: Model.Expr
  for +t: List<&2, Model.Expr>
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for ev: {Optimizer.agree(v, Model.EnvNil{}, h, x) == av : Bool}
  for h1: {Bool.or(Bool.not(aw), o) == True{} : Bool}
  for h2: {Bool.or(Bool.not(o), Bool.not(Bool.xor(aw, av))) == True{} : Bool}
  for ih: {Optimizer.find(t, w, y) == Optimizer.find(filtE(v, t), v, x) : Maybe<&2, Model.Expr>}
  {Optimizer.find.if(h, u => Optimizer.find(t, w, y), aw) == Optimizer.find(filtE.put(h, filtE(v, t), o), v, x) : Maybe<&2, Model.Expr>}

def ff_step(o, aw, av, h, t, v, w, x, y, ev, h1, h2, ih):
  match o aw av:
    case True{} True{} True{}:
      %Equal.sym(Bool, Optimizer.agree(v, Model.EnvNil{}, h, x), True{}, ev) : {Some{h} == Optimizer.find.if(h, u => Optimizer.find(filtE(v, t), v, x), _) : Maybe<&2, Model.Expr>}
      {==}
    case True{} True{} False{}:
      absurd({Some{h} == Optimizer.find.if(h, u => Optimizer.find(filtE(v, t), v, x), Optimizer.agree(v, Model.EnvNil{}, h, x)) : Maybe<&2, Model.Expr>}, bool_clash(h2))
    case True{} False{} True{}:
      absurd({Optimizer.find(t, w, y) == Optimizer.find.if(h, u => Optimizer.find(filtE(v, t), v, x), Optimizer.agree(v, Model.EnvNil{}, h, x)) : Maybe<&2, Model.Expr>}, bool_clash(h2))
    case True{} False{} False{}:
      %Equal.sym(Bool, Optimizer.agree(v, Model.EnvNil{}, h, x), False{}, ev) : {Optimizer.find(t, w, y) == Optimizer.find.if(h, u => Optimizer.find(filtE(v, t), v, x), _) : Maybe<&2, Model.Expr>}
      ih
    case False{} True{} av:
      absurd({Some{h} == Optimizer.find(filtE(v, t), v, x) : Maybe<&2, Model.Expr>}, bool_clash(h1))
    case False{} False{} av:
      ih

law find_filter:
  for +xs: List<&2, Model.Expr>
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +h1: {allh1(xs, v, w, y) == True{} : Bool}
  for +h2: {allh2(xs, v, w, x, y) == True{} : Bool}
  {Optimizer.find(xs, w, y) == Optimizer.find(filtE(v, xs), v, x) : Maybe<&2, Model.Expr>}

def find_filter(xs, v, w, x, y, h1, h2):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      ff_step(over(v, h), Optimizer.agree(w, Model.EnvNil{}, h, y), Optimizer.agree(v, Model.EnvNil{}, h, x), h, t, v, w, x, y, {==}, and_true_left(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, h, y)), over(v, h)), allh1(t, v, w, y), h1), and_true_left(Bool.or(Bool.not(over(v, h)), Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, h, y), Optimizer.agree(v, Model.EnvNil{}, h, x)))), allh2(t, v, w, x, y), h2), find_filter(t, v, w, x, y, and_true_right(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, h, y)), over(v, h)), allh1(t, v, w, y), h1), and_true_right(Bool.or(Bool.not(over(v, h)), Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, h, y), Optimizer.agree(v, Model.EnvNil{}, h, x)))), allh2(t, v, w, x, y), h2)))

law lt_cast:
  for +a: Nat
  for +b: Nat
  for +n: Nat
  for e: {b == n : Nat}
  for h: Lt(a, b)
  Lt(a, n)

def lt_cast(a, b, n, e, h):
  %e : Lt(a, _)
  h

law xnor_eq:
  for +p: Bool
  for +q: Bool
  for e: {p == q : Bool}
  {Bool.not(Bool.xor(p, q)) == True{} : Bool}

def xnor_eq(p, q, e):
  %Equal.sym(Bool, p, q, e) : {Bool.not(Bool.xor(_, q)) == True{} : Bool}
  xnor_refl(q)

law agree_transfer:
  for +c: Model.Expr
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +ocv: {over(v, c) == True{} : Bool}
  for +ocw: {over(w, c) == True{} : Bool}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {Optimizer.agree(w, Model.EnvNil{}, c, y) == Optimizer.agree(v, Model.EnvNil{}, c, x) : Bool}

def agree_transfer(c, v, w, x, y, ocv, ocw, ox, oxw, oy, svw, xy, yx):
  bool_ext(Optimizer.agree(w, Model.EnvNil{}, c, y), Optimizer.agree(v, Model.EnvNil{}, c, x), aw => agree_by(v, Model.EnvNil{}, c, x, +e => Equal.trans(Bool, Model.eval(c, e), Model.eval(y, e), Model.eval(x, e), agree_eval(w, c, y, ocw, oy, aw, e), agree_eval(w, y, x, oy, oxw, yx, e))), av => agree_by(w, Model.EnvNil{}, c, y, +e => Equal.trans(Bool, Model.eval(c, e), Model.eval(x, e), Model.eval(y, e), agree_eval(v, c, x, ocv, ox, av, e), agree_eval(w, x, y, oxw, oy, xy, e))))

law h1_elem:
  for +a: Bool
  for +o: Bool
  for +c: Model.Expr
  for +n: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +ea: {Optimizer.agree(w, Model.EnvNil{}, c, y) == a : Bool}
  for +eo: {over(v, c) == o : Bool}
  for +hok: {ok(w, n, c) == True{} : Bool}
  for +hbw: {below(n, w, y) == True{} : Bool}
  for +ncv: {nonehit(Optimizer.lits(), v, x) == True{} : Bool}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {Bool.or(Bool.not(a), o) == True{} : Bool}

def h1_elem(a, o, c, n, v, w, x, y, ea, eo, hok, hbw, ncv, ox, oxw, oy, svw, xy, yx):
  match a o:
    case False{} o:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      +agr = agree_by(v, Model.EnvNil{}, red(v, c), x, +e => Equal.trans(Bool, Model.eval(red(v, c), e), Model.eval(c, ext(v, e, Model.EnvNil{})), Model.eval(x, e), red_eval(v, c, e), Equal.trans(Bool, Model.eval(c, ext(v, e, Model.EnvNil{})), Model.eval(y, ext(v, e, Model.EnvNil{})), Model.eval(x, e), agree_eval(w, c, y, ok_over(w, n, c, hok), oy, ea, ext(v, e, Model.EnvNil{})), Equal.trans(Bool, Model.eval(y, ext(v, e, Model.EnvNil{})), Model.eval(x, ext(v, e, Model.EnvNil{})), Model.eval(x, e), agree_eval(w, y, x, oy, oxw, yx, ext(v, e, Model.EnvNil{})), eval_ext(v, e, x, ox)))))
      +nl = not_lit(v, x, red(v, c), ncv, agr)
      +orv = good_over(v, red(v, c), red_good(v, c), nl)
      absurd({False{} == True{} : Bool}, below_use(n, w, y, red(v, c), hbw, good_pure(v, red(v, c), red_good(v, c), nl), over_mono(v, w, red(v, c), svw, orv), agree_by(w, Model.EnvNil{}, red(v, c), y, +e => Equal.trans(Bool, Model.eval(red(v, c), e), Model.eval(x, e), Model.eval(y, e), agree_eval(v, red(v, c), x, orv, ox, agr, e), agree_eval(w, x, y, oxw, oy, xy, e))), lt_cast(Model.len(red(v, c)), Model.len(c), n, ok_len(w, n, c, hok), red_strict(v, c, eo, nl))))

law allh1_of:
  for +xs: List<&2, Model.Expr>
  for +n: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +hall: {allok(xs, w, n) == True{} : Bool}
  for +hbw: {below(n, w, y) == True{} : Bool}
  for +ncv: {nonehit(Optimizer.lits(), v, x) == True{} : Bool}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {allh1(xs, v, w, y) == True{} : Bool}

def allh1_of(xs, n, v, w, x, y, hall, hbw, ncv, ox, oxw, oy, svw, xy, yx):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, h, y)), over(v, h)), allh1(t, v, w, y), h1_elem(Optimizer.agree(w, Model.EnvNil{}, h, y), over(v, h), h, n, v, w, x, y, {==}, {==}, and_true_left(ok(w, n, h), allok(t, w, n), hall), hbw, ncv, ox, oxw, oy, svw, xy, yx), allh1_of(t, n, v, w, x, y, and_true_right(ok(w, n, h), allok(t, w, n), hall), hbw, ncv, ox, oxw, oy, svw, xy, yx))

law h2_elem:
  for +o: Bool
  for +c: Model.Expr
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +eo: {over(v, c) == o : Bool}
  for +ocw: {over(w, c) == True{} : Bool}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {Bool.or(Bool.not(o), Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, c, y), Optimizer.agree(v, Model.EnvNil{}, c, x)))) == True{} : Bool}

def h2_elem(o, c, v, w, x, y, eo, ocw, ox, oxw, oy, svw, xy, yx):
  match o:
    case False{}:
      {==}
    case True{}:
      xnor_eq(Optimizer.agree(w, Model.EnvNil{}, c, y), Optimizer.agree(v, Model.EnvNil{}, c, x), agree_transfer(c, v, w, x, y, eo, ocw, ox, oxw, oy, svw, xy, yx))

law allh2_of:
  for +xs: List<&2, Model.Expr>
  for +n: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +hall: {allok(xs, w, n) == True{} : Bool}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {allh2(xs, v, w, x, y) == True{} : Bool}

def allh2_of(xs, n, v, w, x, y, hall, ox, oxw, oy, svw, xy, yx):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_true(Bool.or(Bool.not(over(v, h)), Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, h, y), Optimizer.agree(v, Model.EnvNil{}, h, x)))), allh2(t, v, w, x, y), h2_elem(over(v, h), h, v, w, x, y, {==}, ok_over(w, n, h, and_true_left(ok(w, n, h), allok(t, w, n), hall)), ox, oxw, oy, svw, xy, yx), allh2_of(t, n, v, w, x, y, and_true_right(ok(w, n, h), allok(t, w, n), hall), ox, oxw, oy, svw, xy, yx))

law canon_step:
  for +m: Maybe<&2, Model.Expr>
  for +gv: Nat
  for +gw: Nat
  for +n: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for em: {Optimizer.find(Optimizer.level(n, v), v, x) == m : Maybe<&2, Model.Expr>}
  for emw: {Optimizer.find(Optimizer.level(n, w), w, y) == m : Maybe<&2, Model.Expr>}
  for +hbv: {below(n, v, x) == True{} : Bool}
  for +hbw: {below(n, w, y) == True{} : Bool}
  for ih: {below(1n+n, v, x) == True{} : Bool} -> {below(1n+n, w, y) == True{} : Bool} -> {Optimizer.search(gw, 1n+n, w, y) == Optimizer.search(gv, 1n+n, v, x) : Model.Expr}
  {Optimizer.search.if(u => Optimizer.search(gw, 1n+n, w, y), m) == Optimizer.search.if(u => Optimizer.search(gv, 1n+n, v, x), m) : Model.Expr}

def canon_step(m, gv, gw, n, v, w, x, y, em, emw, hbv, hbw, ih):
  match m:
    case None{}:
      ih(and_true(below(n, v, x), nonehit(Optimizer.level(n, v), v, x), hbv, find_none(Optimizer.level(n, v), v, x, em)), and_true(below(n, w, y), nonehit(Optimizer.level(n, w), w, y), hbw, find_none(Optimizer.level(n, w), w, y, emw)))
    case Some{r}:
      {==}

law search_canon:
  for +fv: Nat
  for +fw: Nat
  for +n: Nat
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  for +filt: {filtS(v, w) == v : List<&2, String>}
  for +ncv: {nonehit(Optimizer.lits(), v, x) == True{} : Bool}
  for +ncw: {nonehit(Optimizer.lits(), w, y) == True{} : Bool}
  for +hbv: {below(n, v, x) == True{} : Bool}
  for +hbw: {below(n, w, y) == True{} : Bool}
  for +hlv: Lt(Model.len(red(v, x)), add_r(fv, n))
  for +hlw: Lt(Model.len(red(w, y)), add_r(fw, n))
  {Optimizer.search(fw, n, w, y) == Optimizer.search(fv, n, v, x) : Model.Expr}

def search_canon(fv, fw, n, v, w, x, y, ox, oxw, oy, svw, xy, yx, filt, ncv, ncw, hbv, hbw, hlv, hlw):
  match fv:
    case 0n:
      +agv = red_agree(v, x, ox)
      +nlv = not_lit(v, x, red(v, x), ncv, agv)
      absurd({Optimizer.search(fw, n, w, y) == x : Model.Expr}, below_use(n, v, x, red(v, x), hbv, good_pure(v, red(v, x), red_good(v, x), nlv), good_over(v, red(v, x), red_good(v, x), nlv), agv, hlv))
    case 1n+gv:
      match fw:
        case 0n:
          +agw = red_agree(w, y, oy)
          +nlw = not_lit(w, y, red(w, y), ncw, agw)
          absurd({y == Optimizer.search(1n+gv, n, v, x) : Model.Expr}, below_use(n, w, y, red(w, y), hbw, good_pure(w, red(w, y), red_good(w, y), nlw), good_over(w, red(w, y), red_good(w, y), nlw), agw, hlw))
        case 1n+gw:
          +keq = Equal.trans(Maybe<&2, Model.Expr>, Optimizer.find(Optimizer.level(n, w), w, y), Optimizer.find(filtE(v, Optimizer.level(n, w)), v, x), Optimizer.find(Optimizer.level(n, v), v, x), find_filter(Optimizer.level(n, w), v, w, x, y, allh1_of(Optimizer.level(n, w), n, v, w, x, y, cands_sound(n, n, False{}, 0n, w), hbw, ncv, ox, oxw, oy, svw, xy, yx), allh2_of(Optimizer.level(n, w), n, v, w, x, y, cands_sound(n, n, False{}, 0n, w), ox, oxw, oy, svw, xy, yx)), Equal.cong(List<&2, Model.Expr>, Maybe<&2, Model.Expr>, z => Optimizer.find(z, v, x), filtE(v, Optimizer.level(n, w)), Optimizer.level(n, v), filtE_cands(n, n, False{}, 0n, v, w, filt)))
          %Equal.sym(Maybe<&2, Model.Expr>, Optimizer.find(Optimizer.level(n, w), w, y), Optimizer.find(Optimizer.level(n, v), v, x), keq) : {Optimizer.search.if(u => Optimizer.search(gw, 1n+n, w, y), _) == Optimizer.search.if(u => Optimizer.search(gv, 1n+n, v, x), Optimizer.find(Optimizer.level(n, v), v, x)) : Model.Expr}
          canon_step(Optimizer.find(Optimizer.level(n, v), v, x), gv, gw, n, v, w, x, y, {==}, keq, hbv, hbw, bv => bw => search_canon(gv, gw, 1n+n, v, w, x, y, ox, oxw, oy, svw, xy, yx, filt, ncv, ncw, bv, bw, hlv, hlw))

law canon_top:
  for +m: Maybe<&2, Model.Expr>
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for em: {Optimizer.find(Optimizer.lits(), v, x) == m : Maybe<&2, Model.Expr>}
  for emw: {Optimizer.find(Optimizer.lits(), w, y) == m : Maybe<&2, Model.Expr>}
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  for +filt: {filtS(v, w) == v : List<&2, String>}
  {Optimizer.search.if(u => Optimizer.search(Model.len(y), 1n, w, y), m) == Optimizer.search.if(u => Optimizer.search(Model.len(x), 1n, v, x), m) : Model.Expr}

def canon_top(m, v, w, x, y, em, emw, ox, oxw, oy, svw, xy, yx, filt):
  match m:
    case None{}:
      search_canon(Model.len(x), Model.len(y), 1n, v, w, x, y, ox, oxw, oy, svw, xy, yx, filt, find_none(Optimizer.lits(), v, x, em), find_none(Optimizer.lits(), w, y, emw), {==}, {==}, witness_len(v, x), witness_len(w, y))
    case Some{r}:
      {==}

law allh1_lits:
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +y: Model.Expr
  {allh1(Optimizer.lits(), v, w, y) == True{} : Bool}

def allh1_lits(v, w, y):
  and_true(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{False{}}, y)), True{}), allh1(Model.Lit{True{}} <> Nil{}, v, w, y), or_true_right(Bool.not(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{False{}}, y)), True{}, {==}), and_true(Bool.or(Bool.not(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{True{}}, y)), True{}), True{}, or_true_right(Bool.not(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{True{}}, y)), True{}, {==}), {==}))

law allh2_lits:
  for +v: List<&2, String>
  for +w: List<&2, String>
  for +x: Model.Expr
  for +y: Model.Expr
  for +ox: {over(v, x) == True{} : Bool}
  for +oxw: {over(w, x) == True{} : Bool}
  for +oy: {over(w, y) == True{} : Bool}
  for +svw: {subb(v, w) == True{} : Bool}
  for +xy: {Optimizer.agree(w, Model.EnvNil{}, x, y) == True{} : Bool}
  for +yx: {Optimizer.agree(w, Model.EnvNil{}, y, x) == True{} : Bool}
  {allh2(Optimizer.lits(), v, w, x, y) == True{} : Bool}

def allh2_lits(v, w, x, y, ox, oxw, oy, svw, xy, yx):
  and_true(Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{False{}}, y), Optimizer.agree(v, Model.EnvNil{}, Model.Lit{False{}}, x))), allh2(Model.Lit{True{}} <> Nil{}, v, w, x, y), xnor_eq(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{False{}}, y), Optimizer.agree(v, Model.EnvNil{}, Model.Lit{False{}}, x), agree_transfer(Model.Lit{False{}}, v, w, x, y, {==}, {==}, ox, oxw, oy, svw, xy, yx)), and_true(Bool.not(Bool.xor(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{True{}}, y), Optimizer.agree(v, Model.EnvNil{}, Model.Lit{True{}}, x))), True{}, xnor_eq(Optimizer.agree(w, Model.EnvNil{}, Model.Lit{True{}}, y), Optimizer.agree(v, Model.EnvNil{}, Model.Lit{True{}}, x), agree_transfer(Model.Lit{True{}}, v, w, x, y, {==}, {==}, ox, oxw, oy, svw, xy, yx)), {==}))

law canon_core:
  for +x: Model.Expr
  for +y: Model.Expr
  for +filt: {filtS(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{})) == Optimizer.uniq(Optimizer.vars(x), Nil{}) : List<&2, String>}
  for +svw: {subb(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{})) == True{} : Bool}
  for q: @e: Model.Env -> {Model.eval(y, e) == Model.eval(x, e) : Bool}
  {Optimizer.optimize(y) == Optimizer.optimize(x) : Model.Expr}

def canon_core(x, y, filt, svw, q):
  +ox = over_vars(x)
  +oy = over_vars(y)
  +oxw = over_mono(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{}), x, svw, ox)
  +yx = agree_by(Optimizer.uniq(Optimizer.vars(y), Nil{}), Model.EnvNil{}, y, x, q)
  +xy = agree_by(Optimizer.uniq(Optimizer.vars(y), Nil{}), Model.EnvNil{}, x, y, +e => Equal.sym(Bool, Model.eval(y, e), Model.eval(x, e), agree_eval(Optimizer.uniq(Optimizer.vars(y), Nil{}), y, x, oy, oxw, yx, e)))
  +keq = find_filter(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{}), x, y, allh1_lits(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{}), y), allh2_lits(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{}), x, y, ox, oxw, oy, svw, xy, yx))
  %Equal.sym(Maybe<&2, Model.Expr>, Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(y), Nil{}), y), Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x), keq) : {Optimizer.search.if(u => Optimizer.search(Model.len(y), 1n, Optimizer.uniq(Optimizer.vars(y), Nil{}), y), _) == Optimizer.search.if(u => Optimizer.search(Model.len(x), 1n, Optimizer.uniq(Optimizer.vars(x), Nil{}), x), Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x)) : Model.Expr}
  canon_top(Optimizer.find(Optimizer.lits(), Optimizer.uniq(Optimizer.vars(x), Nil{}), x), Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{}), x, y, {==}, keq, ox, oxw, oy, svw, xy, yx, filt)

law canon:
  for +x: Model.Expr
  for +y: Model.Expr
  for +zs: List<&2, String>
  for +hv: {Optimizer.vars(y) == Optimizer.cat(Optimizer.vars(x), zs) : List<&2, String>}
  for q: @e: Model.Env -> {Model.eval(y, e) == Model.eval(x, e) : Bool}
  {Optimizer.optimize(y) == Optimizer.optimize(x) : Model.Expr}

def canon(x, y, zs, hv, q):
  canon_core(x, y, Equal.trans(List<&2, String>, filtS(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{})), filtS(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.cat(Optimizer.vars(x), zs), Nil{})), Optimizer.uniq(Optimizer.vars(x), Nil{}), Equal.cong(List<&2, String>, List<&2, String>, z => filtS(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(z, Nil{})), Optimizer.vars(y), Optimizer.cat(Optimizer.vars(x), zs), hv), uniq_prefix(Optimizer.vars(x), zs)), Equal.trans(Bool, subb(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.vars(y), Nil{})), subb(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(Optimizer.cat(Optimizer.vars(x), zs), Nil{})), True{}, Equal.cong(List<&2, String>, Bool, z => subb(Optimizer.uniq(Optimizer.vars(x), Nil{}), Optimizer.uniq(z, Nil{})), Optimizer.vars(y), Optimizer.cat(Optimizer.vars(x), zs), hv), uniq_prefix_sub(Optimizer.vars(x), zs)), q)

def Laws.folds_not_true():
  const_result(Model.Not{Model.Lit{True{}}}, False{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.Not{Model.Lit{True{}}}), Nil{}), Model.EnvNil{}, Model.Lit{False{}}, Model.Not{Model.Lit{True{}}}, +e => {==}))

def Laws.folds_not_false():
  const_result(Model.Not{Model.Lit{False{}}}, True{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.Not{Model.Lit{False{}}}), Nil{}), Model.EnvNil{}, Model.Lit{True{}}, Model.Not{Model.Lit{False{}}}, +e => {==}))

def Laws.simplifies_and_false(expr):
  +expr = expr
  const_result(Model.And{Model.Lit{False{}}, expr}, False{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.And{Model.Lit{False{}}, expr}), Nil{}), Model.EnvNil{}, Model.Lit{False{}}, Model.And{Model.Lit{False{}}, expr}, +e => {==}))

def Laws.simplifies_or_true(expr):
  +expr = expr
  const_result(Model.Or{Model.Lit{True{}}, expr}, True{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.Or{Model.Lit{True{}}, expr}), Nil{}), Model.EnvNil{}, Model.Lit{True{}}, Model.Or{Model.Lit{True{}}, expr}, +e => {==}))

def Laws.simplifies_and_false_right(expr):
  +expr = expr
  const_result(Model.And{expr, Model.Lit{False{}}}, False{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.And{expr, Model.Lit{False{}}}), Nil{}), Model.EnvNil{}, Model.Lit{False{}}, Model.And{expr, Model.Lit{False{}}}, +e => Equal.sym(Bool, Bool.and(Model.eval(expr, e), False{}), False{}, bool_and_false(Model.eval(expr, e)))))

def Laws.simplifies_or_true_right(expr):
  +expr = expr
  const_result(Model.Or{expr, Model.Lit{True{}}}, True{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.Or{expr, Model.Lit{True{}}}), Nil{}), Model.EnvNil{}, Model.Lit{True{}}, Model.Or{expr, Model.Lit{True{}}}, +e => Equal.sym(Bool, Bool.or(Model.eval(expr, e), True{}), True{}, bool_or_true(Model.eval(expr, e)))))

def Laws.removes_contradiction(expr):
  +expr = expr
  const_result(Model.And{expr, Model.Not{expr}}, False{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.And{expr, Model.Not{expr}}), Nil{}), Model.EnvNil{}, Model.Lit{False{}}, Model.And{expr, Model.Not{expr}}, +e => Equal.sym(Bool, Bool.and(Model.eval(expr, e), Bool.not(Model.eval(expr, e))), False{}, bool_and_not_self(Model.eval(expr, e)))))

def Laws.removes_excluded_middle(expr):
  +expr = expr
  const_result(Model.Or{expr, Model.Not{expr}}, True{}, agree_by(Optimizer.uniq(Optimizer.vars(Model.Or{expr, Model.Not{expr}}), Nil{}), Model.EnvNil{}, Model.Lit{True{}}, Model.Or{expr, Model.Not{expr}}, +e => Equal.sym(Bool, Bool.or(Model.eval(expr, e), Bool.not(Model.eval(expr, e))), True{}, bool_or_not_self(Model.eval(expr, e)))))

def Laws.removes_double_not(expr):
  +expr = expr
  canon(expr, Model.Not{Model.Not{expr}}, Nil{}, Equal.sym(List<&2, String>, Optimizer.cat(Optimizer.vars(expr), Nil{}), Optimizer.vars(expr), cat_nil(Optimizer.vars(expr))), +e => bool_not_not(Model.eval(expr, e)))

def Laws.simplifies_and_true(expr):
  +expr = expr
  canon(expr, Model.And{Model.Lit{True{}}, expr}, Nil{}, Equal.sym(List<&2, String>, Optimizer.cat(Optimizer.vars(expr), Nil{}), Optimizer.vars(expr), cat_nil(Optimizer.vars(expr))), +e => {==})

def Laws.simplifies_or_false(expr):
  +expr = expr
  canon(expr, Model.Or{Model.Lit{False{}}, expr}, Nil{}, Equal.sym(List<&2, String>, Optimizer.cat(Optimizer.vars(expr), Nil{}), Optimizer.vars(expr), cat_nil(Optimizer.vars(expr))), +e => {==})

def Laws.simplifies_and_true_right(expr):
  +expr = expr
  canon(expr, Model.And{expr, Model.Lit{True{}}}, Nil{}, {==}, +e => bool_and_true(Model.eval(expr, e)))

def Laws.simplifies_or_false_right(expr):
  +expr = expr
  canon(expr, Model.Or{expr, Model.Lit{False{}}}, Nil{}, {==}, +e => bool_or_false(Model.eval(expr, e)))

def Laws.de_morgan_and(left, right):
  +left = left
  +right = right
  canon(Model.Or{Model.Not{left}, Model.Not{right}}, Model.Not{Model.And{left, right}}, Nil{}, Equal.sym(List<&2, String>, Optimizer.cat(Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), Nil{}), Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), cat_nil(Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)))), +e => Equal.sym(Bool, Bool.or(Bool.not(Model.eval(left, e)), Bool.not(Model.eval(right, e))), Bool.not(Bool.and(Model.eval(left, e), Model.eval(right, e))), bool_or_not(Model.eval(left, e), Model.eval(right, e))))

def Laws.de_morgan_or(left, right):
  +left = left
  +right = right
  canon(Model.And{Model.Not{left}, Model.Not{right}}, Model.Not{Model.Or{left, right}}, Nil{}, Equal.sym(List<&2, String>, Optimizer.cat(Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), Nil{}), Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), cat_nil(Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)))), +e => Equal.sym(Bool, Bool.and(Bool.not(Model.eval(left, e)), Bool.not(Model.eval(right, e))), Bool.not(Bool.or(Model.eval(left, e), Model.eval(right, e))), bool_and_not(Model.eval(left, e), Model.eval(right, e))))

def Laws.and_idempotent(expr):
  +expr = expr
  canon(expr, Model.And{expr, expr}, Optimizer.vars(expr), {==}, +e => bool_and_self(Model.eval(expr, e)))

def Laws.or_idempotent(expr):
  +expr = expr
  canon(expr, Model.Or{expr, expr}, Optimizer.vars(expr), {==}, +e => bool_or_self(Model.eval(expr, e)))

def Laws.absorbs_and_in_or(left, right):
  +left = left
  +right = right
  canon(left, Model.Or{left, Model.And{left, right}}, Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), {==}, +e => bool_or_and(Model.eval(left, e), Model.eval(right, e)))

def Laws.absorbs_or_in_and(left, right):
  +left = left
  +right = right
  canon(left, Model.And{left, Model.Or{left, right}}, Optimizer.cat(Optimizer.vars(left), Optimizer.vars(right)), {==}, +e => bool_and_or(Model.eval(left, e), Model.eval(right, e)))
