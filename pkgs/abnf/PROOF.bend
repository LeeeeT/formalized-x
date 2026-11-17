# Proofs of LAWS.bend.
#
# One matcher, `sem`, does all the work. `limit(d, g)` runs it with fuel `1+d`.
# `full(g)` runs it with fuel `1+bound(g, s)`, and the bound is proved complete
# below (see `complete`).

import Base
import ./LAWS.bend as L

type R is Data:
  Emp{}
  Bad{}
  Lit{c: Char}
  Rng{lo: U32, hi: U32}
  Cat{a: R, b: R}
  Alt{a: R, b: R}
  Star{r: R}
  Ref{name: String}

type Gram is Data:
  GNil{}
  GCon{k: String, r: R, t: Gram}

type Bk is Data:
  Limit{d: Nat, g: Gram}
  Full{g: Gram}

# ---- the matcher ----

def then(a: Bool, k: Unit -> Bool) -> Bool:
  match a:
    case False{}:
      False{}
    case True{}:
      k(Unit{})

def orelse(a: Bool, k: Unit -> Bool) -> Bool:
  match a:
    case False{}:
      k(Unit{})
    case True{}:
      True{}

def lk.pick(e: Bool, r: R, rest: R) -> R:
  match e:
    case False{}:
      rest
    case True{}:
      Alt{r, rest}

def lk(g: Gram, +n: String) -> R:
  match g:
    case GNil{}:
      Bad{}
    case GCon{k, r, t}:
      lk.pick(String.eq(String.to_lower(k), String.to_lower(n)), r, lk(t, n))

def isle(+lo: U32, +x: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# sem(d, g, r, x, p): r matches x. `p` is the prefix a `Cat` or `Star` has
# already consumed while looking for a split of p ++ x; it is "" everywhere else.
def sem(+d: Nat, +g: Gram, r: R, +x: String, +p: String) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+e:
      match r:
        case Emp{}:
          String.is_empty(x)
        case Bad{}:
          False{}
        case Lit{c}:
          match x:
            case SNil{}:
              False{}
            case SCon{h, t}:
              match t:
                case SNil{}:
                  Char.is_eq(c, h)
                case SCon{h2, t2}:
                  False{}
        case Rng{+lo, +hi}:
          match x:
            case SNil{}:
              False{}
            case SCon{h, t}:
              match t:
                case SNil{}:
                  isle(lo, Char.to_u32(h), hi)
                case SCon{h2, t2}:
                  False{}
        case Cat{+a, +b}:
          match x:
            case SNil{}:
              then(sem(d, g, a, p, ""), u => sem(d, g, b, SNil{}, ""))
            case SCon{h, t}:
              orelse(then(sem(d, g, a, p, ""), u => sem(d, g, b, SCon{h, t}, "")), u => sem(d, g, Cat{a, b}, t, p ++ SCon{h, SNil{}}))
        case Alt{+a, +b}:
          orelse(sem(d, g, a, x, ""), u => sem(d, g, b, x, ""))
        case Star{+a}:
          match x:
            case SNil{}:
              orelse(String.is_empty(p), u => sem(d, g, a, p, ""))
            case SCon{h, t}:
              orelse(then(sem(d, g, a, p, ""), u => sem(d, g, Star{a}, t, SCon{h, SNil{}})), u => sem(d, g, Star{a}, t, p ++ SCon{h, SNil{}}))
        case Ref{n}:
          sem(e, g, lk(g, n), x, "")

# ---- Bool, Nat and String facts ----

def T(b: Bool) -> Data:
  {b == True{} : Bool}

def Bool.imp(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

def false.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false.empty:
  for h: T(False{})
  Empty

def false.empty(h):
  %h : false.disc(_)
  Unit{}

def absurd(-A: Type, e: Empty) -> A:
  match e:

def false.elim(-A: Type, h: T(False{})) -> A:
  absurd(A, false.empty(h))

def succ.disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law succ.empty:
  for -n: Nat
  for h: {1n+n == 0n : Nat}
  Empty

def succ.empty(n, h):
  %h : succ.disc(_)
  Unit{}

law app.nil:
  for a: String
  {a ++ "" == a : String}

def app.nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %app.nil(t) : {SCon{h, t ++ ""} == SCon{h, _} : String}
      {==}

law app.assoc:
  for a: String
  for -b: String
  for -c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}

def app.assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %app.assoc(t, b, c) : {SCon{h, (t ++ b) ++ c} == SCon{h, _} : String}
      {==}

law add.zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def add.zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add.zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add.succ:
  for a: Nat
  for -b: Nat
  {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}

def add.succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add.succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

law add.left_comm:
  for +x: Nat
  for y: Nat
  for -z: Nat
  {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}

def add.left_comm(x, y, z):
  match y:
    case 0n:
      {==}
    case 1n+p:
      %add.succ(x, Nat.add(p, z)) : {_ == 1n+Nat.add(p, Nat.add(x, z)) : Nat}
      %add.left_comm(x, p, z) : {1n+Nat.add(x, Nat.add(p, z)) == 1n+_ : Nat}
      {==}

law add.swap4:
  for d: Nat
  for +a: Nat
  for +e: Nat
  for -b: Nat
  {Nat.add(Nat.add(d, a), Nat.add(e, b)) == Nat.add(Nat.add(d, e), Nat.add(a, b)) : Nat}

def add.swap4(d, a, e, b):
  match d:
    case 0n:
      add.left_comm(a, e, b)
    case 1n+p:
      %add.swap4(p, a, e, b) : {1n+Nat.add(Nat.add(p, a), Nat.add(e, b)) == 1n+_ : Nat}
      {==}

law add.zero_l:
  for a: Nat
  for -b: Nat
  for h: {Nat.add(a, b) == 0n : Nat}
  {a == 0n : Nat}

def add.zero_l(a, b, h):
  match a:
    case 0n:
      {==}
    case 1n+p:
      absurd({1n+p == 0n : Nat}, succ.empty(Nat.add(p, b), h))

law add.zero_r:
  for a: Nat
  for -b: Nat
  for h: {Nat.add(a, b) == 0n : Nat}
  {b == 0n : Nat}

def add.zero_r(a, b, h):
  match a:
    case 0n:
      h
    case 1n+p:
      absurd({b == 0n : Nat}, succ.empty(Nat.add(p, b), h))

law app.nil.sym:
  for a: String
  {a == a ++ "" : String}

def app.nil.sym(a):
  Equal.sym(String, a ++ "", a, app.nil(a))

law app.assoc.sym:
  for a: String
  for -b: String
  for -c: String
  {a ++ (b ++ c) == (a ++ b) ++ c : String}

def app.assoc.sym(a, b, c):
  Equal.sym(String, (a ++ b) ++ c, a ++ (b ++ c), app.assoc(a, b, c))

law add.zeros:
  for a: Nat
  for -b: Nat
  for ha: {a == 0n : Nat}
  for hb: {b == 0n : Nat}
  {Nat.add(a, b) == 0n : Nat}

def add.zeros(a, b, ha, hb):
  match a:
    case 0n:
      hb
    case 1n+p:
      absurd({Nat.add(1n+p, b) == 0n : Nat}, succ.empty(p, ha))

# ---- U32 arithmetic, for compact ranges ----

# Nat order against doubling
def bdbl(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

law cmp.dbl.go:
  for x: Nat
  for y: Nat
  for a: Bool
  for b: Bool
  {Nat.cmp(bdbl(a, x), bdbl(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}

def cmp.dbl.go(x, y, a, b):
  match x y:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match a b:
        case False{} False{}:
          cmp.dbl.go(p, q, False{}, False{})
        case False{} True{}:
          cmp.dbl.go(p, q, False{}, True{})
        case True{} False{}:
          cmp.dbl.go(p, q, True{}, False{})
        case True{} True{}:
          cmp.dbl.go(p, q, True{}, True{})

law cmp.word:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  {Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.cmp(n, a, b) : Cmp}

def cmp.word(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %cmp.word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{False{}, bt})) == Word.cmp.fin(False{}, False{}, _) : Cmp}
          cmp.dbl.go(Word.to_nat(p, at), Word.to_nat(p, bt), False{}, False{})
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %cmp.word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{True{}, bt})) == Word.cmp.fin(False{}, True{}, _) : Cmp}
          cmp.dbl.go(Word.to_nat(p, at), Word.to_nat(p, bt), False{}, True{})
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %cmp.word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{False{}, bt})) == Word.cmp.fin(True{}, False{}, _) : Cmp}
          cmp.dbl.go(Word.to_nat(p, at), Word.to_nat(p, bt), True{}, False{})
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %cmp.word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{True{}, bt})) == Word.cmp.fin(True{}, True{}, _) : Cmp}
          cmp.dbl.go(Word.to_nat(p, at), Word.to_nat(p, bt), True{}, True{})

def cmp.disc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

law eq.not.lt:
  for h: {EQ{} == LT{} : Cmp}
  Empty

def eq.not.lt(h):
  %h : cmp.disc(_)
  Unit{}

law gt.not.lt:
  for h: {GT{} == LT{} : Cmp}
  Empty

def gt.not.lt(h):
  %h : cmp.disc(_)
  Unit{}

law fin.lt:
  for bz: Bool
  for c: Cmp
  for h: {Word.cmp.fin(True{}, bz, c) == LT{} : Cmp}
  {c == LT{} : Cmp}

def fin.lt(bz, c, h):
  match bz c:
    case _ LT{}:
      {==}
    case False{} EQ{}:
      absurd({EQ{} == LT{} : Cmp}, gt.not.lt(h))
    case True{} EQ{}:
      absurd({EQ{} == LT{} : Cmp}, eq.not.lt(h))
    case _ GT{}:
      absurd({GT{} == LT{} : Cmp}, gt.not.lt(h))

law w.inc.nat:
  for +n: Nat
  for w: Word(n)
  for z: Word(n)
  for h: {Word.cmp(n, w, z) == LT{} : Cmp}
  {1n+Word.to_nat(n, w) == Word.to_nat(n, Word.inc(n, w)) : Nat}

def w.inc.nat(n, w, z, h):
  match n:
    case 0n:
      absurd({1n+Word.to_nat(0n, w) == Word.to_nat(0n, Word.inc(0n, w)) : Nat}, eq.not.lt(h))
    case 1n+p:
      match w z:
        case WCon{False{}, t} WCon{bz, tz}:
          {==}
        case WCon{True{}, +t} WCon{bz, +tz}:
          %w.inc.nat(p, t, tz, fin.lt(bz, Word.cmp(p, t, tz), h)) : {2n+Nat.double(Word.to_nat(p, t)) == Nat.double(_) : Nat}
          {==}

def cinc(n: Nat, a: Word(n), c: Bool) -> Word(n):
  match c:
    case False{}:
      a
    case True{}:
      Word.inc(n, a)

law w.adc.zero:
  for +n: Nat
  for a: Word(n)
  for c: Bool
  {Word.adc(n, a, Word.zero(n), False{}, c) == cinc(n, a, c) : Word(n)}

def w.adc.zero(n, a, c):
  match n:
    case 0n:
      match a c:
        case WNil{} False{}:
          {==}
        case WNil{} True{}:
          {==}
    case 1n+p:
      match a c:
        case WCon{False{}, +t} False{}:
          %w.adc.zero(p, t, False{}) : {WCon{False{}, Word.adc(p, t, Word.zero(p), False{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} False{}:
          %w.adc.zero(p, t, False{}) : {WCon{True{}, Word.adc(p, t, Word.zero(p), False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} True{}:
          %w.adc.zero(p, t, False{}) : {WCon{True{}, Word.adc(p, t, Word.zero(p), False{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} True{}:
          %w.adc.zero(p, t, True{}) : {WCon{False{}, Word.adc(p, t, Word.zero(p), False{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}

law w.add1:
  for +n: Nat
  for w: Word(1n+n)
  {Word.adc(1n+n, w, WCon{True{}, Word.zero(n)}, False{}, False{}) == Word.inc(1n+n, w) : Word(1n+n)}

def w.add1(n, w):
  match w:
    case WCon{False{}, +t}:
      %w.adc.zero(n, t, False{}) : {WCon{True{}, Word.adc(n, t, Word.zero(n), False{}, False{})} == WCon{True{}, _} : Word(1n+n)}
      {==}
    case WCon{True{}, +t}:
      %w.adc.zero(n, t, True{}) : {WCon{False{}, Word.adc(n, t, Word.zero(n), False{}, True{})} == WCon{False{}, _} : Word(1n+n)}
      {==}

law u32.add1:
  for x: U32
  {U32.add(x, 1) == U32.inc(x) : U32}

def u32.add1(x):
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.adc(32n, w, WCon{True{}, Word.zero(31n)}, False{}, False{}), Word.inc(32n, w), w.add1(31n, w))

def N(u: U32) -> Nat:
  U32.to_nat(u)

law u32.le.nat:
  for a: U32
  for b: U32
  {Nat.is_le(N(a), N(b)) == U32.is_le(a, b) : Bool}

def u32.le.nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Cmp, Bool, c => Cmp.is_le(c), Nat.cmp(Word.to_nat(32n, x), Word.to_nat(32n, y)), Word.cmp(32n, x, y), cmp.word(32n, x, y))

law u32.eq.nat:
  for a: U32
  for b: U32
  {Nat.is_eq(N(a), N(b)) == U32.is_eq(a, b) : Bool}

def u32.eq.nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Nat.cmp(Word.to_nat(32n, x), Word.to_nat(32n, y)), Word.cmp(32n, x, y), cmp.word(32n, x, y))

law u32.cmp.nat:
  for a: U32
  for b: U32
  {Nat.cmp(N(a), N(b)) == U32.cmp(a, b) : Cmp}

def u32.cmp.nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      cmp.word(32n, x, y)

law nat.lt.cmp:
  for a: Nat
  for b: Nat
  for h: T(Nat.is_le(1n+a, b))
  {Nat.cmp(a, b) == LT{} : Cmp}

def nat.lt.cmp(a, b, h):
  match a b:
    case _ 0n:
      false.elim({Nat.cmp(a, 0n) == LT{} : Cmp}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      nat.lt.cmp(p, q, h)

law u32.lt.w:
  for +x: Word(32n)
  for +z: Word(32n)
  for h: T(Nat.is_le(1n+Word.to_nat(32n, x), Word.to_nat(32n, z)))
  {Word.cmp(32n, x, z) == LT{} : Cmp}

def u32.lt.w(x, z, h):
  %cmp.word(32n, x, z) : {_ == LT{} : Cmp}
  nat.lt.cmp(Word.to_nat(32n, x), Word.to_nat(32n, z), h)

law u32.succ.nat:
  for c: U32
  for H: U32
  for h: T(Nat.is_le(1n+N(c), N(H)))
  {1n+N(c) == N(U32.add(c, 1)) : Nat}

def u32.succ.nat(c, H, h):
  match c H:
    case U32{+x} U32{+z}:
      %Equal.sym(U32, U32.add(U32{x}, 1), U32.inc(U32{x}), u32.add1(U32{x})) : {1n+N(U32{x}) == N(_) : Nat}
      w.inc.nat(32n, x, z, u32.lt.w(x, z, h))

# ---- substrings ----

# `u ++ (y ++ v) == S` says that y is a substring of S. These move that fact
# from the whole `p ++ x` to its pieces.

law sub.left:
  for -u: String
  for p: String
  for -x: String
  for -v: String
  for -S: String
  for h: {u ++ ((p ++ x) ++ v) == S : String}
  {u ++ (p ++ (x ++ v)) == S : String}

def sub.left(u, p, x, v, S, h):
  %app.assoc(p, x, v) : {u ++ _ == S : String}
  h

law sub.right:
  for u: String
  for +p: String
  for +x: String
  for -v: String
  for -S: String
  for h: {u ++ ((p ++ x) ++ v) == S : String}
  {(u ++ p) ++ (x ++ v) == S : String}

def sub.right(u, p, x, v, S, h):
  %app.assoc.sym(u, p, x ++ v) : {_ == S : String}
  sub.left(u, p, x, v, S, h)

law sub.snoc:
  for -u: String
  for p: String
  for -c: Char
  for -t: String
  for -v: String
  for -S: String
  for h: {u ++ ((p ++ SCon{c, t}) ++ v) == S : String}
  {u ++ (((p ++ SCon{c, SNil{}}) ++ t) ++ v) == S : String}

def sub.snoc(u, p, c, t, v, S, h):
  %app.assoc.sym(p, SCon{c, SNil{}}, t) : {u ++ (_ ++ v) == S : String}
  h

# ---- more fuel never hurts ----

law imp.refl:
  for a: Bool
  T(Bool.imp(a, a))

def imp.refl(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law imp.true:
  for a: Bool
  T(Bool.imp(a, True{}))

def imp.true(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law imp.mp:
  for a: Bool
  for -b: Bool
  for hi: T(Bool.imp(a, b))
  for ha: T(a)
  T(b)

def imp.mp(a, b, hi, ha):
  match a:
    case False{}:
      false.elim(T(b), ha)
    case True{}:
      hi

law mono.then:
  for a: Bool
  for a2: Bool
  for -b: Bool
  for -b2: Bool
  for h1: T(Bool.imp(a, a2))
  for h2: T(Bool.imp(b, b2))
  T(Bool.imp(then(a, u => b), then(a2, u => b2)))

def mono.then(a, a2, b, b2, h1, h2):
  match a a2:
    case False{} _:
      {==}
    case True{} False{}:
      false.elim(T(Bool.imp(b, False{})), h1)
    case True{} True{}:
      h2

law mono.or:
  for a: Bool
  for a2: Bool
  for b: Bool
  for -b2: Bool
  for h1: T(Bool.imp(a, a2))
  for h2: T(Bool.imp(b, b2))
  T(Bool.imp(orelse(a, u => b), orelse(a2, u => b2)))

def mono.or(a, a2, b, b2, h1, h2):
  match a a2:
    case False{} False{}:
      h2
    case False{} True{}:
      imp.true(b)
    case True{} False{}:
      false.elim(T(Bool.imp(True{}, b2)), h1)
    case True{} True{}:
      {==}

law mono:
  for +d: Nat
  for +g: Gram
  for r: R
  for +x: String
  for +p: String
  T(Bool.imp(sem(d, g, r, x, p), sem(1n+d, g, r, x, p)))

def mono(d, g, r, x, p):
  match d:
    case 0n:
      {==}
    case 1n+e:
      match r:
        case Emp{}:
          imp.refl(String.is_empty(x))
        case Bad{}:
          {==}
        case Lit{+c}:
          match x:
            case SNil{}:
              {==}
            case SCon{h, t}:
              match t:
                case SNil{}:
                  imp.refl(Char.is_eq(c, h))
                case SCon{h2, t2}:
                  {==}
        case Rng{+lo, +hi}:
          match x:
            case SNil{}:
              {==}
            case SCon{h, t}:
              match t:
                case SNil{}:
                  imp.refl(isle(lo, Char.to_u32(h), hi))
                case SCon{h2, t2}:
                  {==}
        case Cat{+a, +b}:
          match x:
            case SNil{}:
              mono.then(sem(d, g, a, p, ""), sem(1n+d, g, a, p, ""), sem(d, g, b, SNil{}, ""), sem(1n+d, g, b, SNil{}, ""), mono(d, g, a, p, ""), mono(d, g, b, SNil{}, ""))
            case SCon{h, t}:
              mono.or(then(sem(d, g, a, p, ""), u => sem(d, g, b, SCon{h, t}, "")), then(sem(1n+d, g, a, p, ""), u => sem(1n+d, g, b, SCon{h, t}, "")), sem(d, g, Cat{a, b}, t, p ++ SCon{h, SNil{}}), sem(1n+d, g, Cat{a, b}, t, p ++ SCon{h, SNil{}}), mono.then(sem(d, g, a, p, ""), sem(1n+d, g, a, p, ""), sem(d, g, b, SCon{h, t}, ""), sem(1n+d, g, b, SCon{h, t}, ""), mono(d, g, a, p, ""), mono(d, g, b, SCon{h, t}, "")), mono(d, g, Cat{a, b}, t, p ++ SCon{h, SNil{}}))
        case Alt{+a, +b}:
          mono.or(sem(d, g, a, x, ""), sem(1n+d, g, a, x, ""), sem(d, g, b, x, ""), sem(1n+d, g, b, x, ""), mono(d, g, a, x, ""), mono(d, g, b, x, ""))
        case Star{+a}:
          match x:
            case SNil{}:
              mono.or(String.is_empty(p), String.is_empty(p), sem(d, g, a, p, ""), sem(1n+d, g, a, p, ""), imp.refl(String.is_empty(p)), mono(d, g, a, p, ""))
            case SCon{h, t}:
              mono.or(then(sem(d, g, a, p, ""), u => sem(d, g, Star{a}, t, SCon{h, SNil{}})), then(sem(1n+d, g, a, p, ""), u => sem(1n+d, g, Star{a}, t, SCon{h, SNil{}})), sem(d, g, Star{a}, t, p ++ SCon{h, SNil{}}), sem(1n+d, g, Star{a}, t, p ++ SCon{h, SNil{}}), mono.then(sem(d, g, a, p, ""), sem(1n+d, g, a, p, ""), sem(d, g, Star{a}, t, SCon{h, SNil{}}), sem(1n+d, g, Star{a}, t, SCon{h, SNil{}}), mono(d, g, a, p, ""), mono(d, g, Star{a}, t, SCon{h, SNil{}})), mono(d, g, Star{a}, t, p ++ SCon{h, SNil{}}))
        case Ref{+n}:
          mono(e, g, lk(g, n), x, "")

law mono.add:
  for +k: Nat
  for +d: Nat
  for +g: Gram
  for +r: R
  for +x: String
  for +p: String
  for h: T(sem(d, g, r, x, p))
  T(sem(Nat.add(k, d), g, r, x, p))

def mono.add(k, d, g, r, x, p, h):
  match k:
    case 0n:
      h
    case 1n+j:
      imp.mp(sem(Nat.add(j, d), g, r, x, p), sem(1n+Nat.add(j, d), g, r, x, p), mono(Nat.add(j, d), g, r, x, p), mono.add(j, d, g, r, x, p, h))

# ---- counting undecided pairs ----

# The live bound: one level of `bound` per (rule, substring) pair of the input.

def capG(g: Gram) -> Nat:
  match g:
    case GNil{}:
      0n
    case GCon{k, r, t}:
      1n+capG(t)

def capP(+n: Nat, x: String) -> Nat:
  match x:
    case SNil{}:
      n
    case SCon{h, t}:
      Nat.add(n, capP(n, t))

def capS(+n: Nat, s: String) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{+h, +t}:
      Nat.add(capP(n, SCon{h, t}), capS(n, t))

def bound(g: Gram, s: String) -> Nat:
  capS(capG(g), s)

# Dead counters over every (rule of g, substring of s). With m = False{} they
# count the pairs not yet matched at fuel d; with m = True{}, the pairs whose
# answer changes between fuel d and fuel 1+d.

def bv(b: Bool) -> Nat:
  match b:
    case False{}:
      1n
    case True{}:
      0n

def xv(a: Bool, b: Bool) -> Nat:
  match a b:
    case False{} False{}:
      0n
    case False{} True{}:
      1n
    case True{} False{}:
      1n
    case True{} True{}:
      0n

def wt(m: Bool, +d: Nat, +g: Gram, +r: R, +y: String) -> Nat:
  match m:
    case False{}:
      bv(sem(d, g, r, y, ""))
    case True{}:
      xv(sem(d, g, r, y, ""), sem(1n+d, g, r, y, ""))

def sG(+m: Bool, +d: Nat, +g: Gram, G: Gram, +y: String) -> Nat:
  match G:
    case GNil{}:
      0n
    case GCon{k, +r, t}:
      Nat.add(wt(m, d, g, r, y), sG(m, d, g, t, y))

def sP(+m: Bool, +d: Nat, +g: Gram, x: String, +pre: String) -> Nat:
  match x:
    case SNil{}:
      sG(m, d, g, g, pre)
    case SCon{h, t}:
      Nat.add(sG(m, d, g, g, pre), sP(m, d, g, t, pre ++ SCon{h, SNil{}}))

def sS(+m: Bool, +d: Nat, +g: Gram, s: String) -> Nat:
  match s:
    case SNil{}:
      sP(m, d, g, SNil{}, "")
    case SCon{+h, +t}:
      Nat.add(sP(m, d, g, SCon{h, t}, ""), sS(m, d, g, t))

law key.eq:
  for a: Bool
  for b: Bool
  for h: T(Bool.imp(a, b))
  {Nat.add(xv(a, b), bv(b)) == bv(a) : Nat}

def key.eq(a, b, h):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      false.elim({Nat.add(1n, 1n) == 0n : Nat}, h)
    case True{} True{}:
      {==}

law add.hom:
  for -a: Nat
  for -b: Nat
  for da: Nat
  for +a2: Nat
  for +db: Nat
  for -b2: Nat
  for ha: {Nat.add(da, a2) == a : Nat}
  for hb: {Nat.add(db, b2) == b : Nat}
  {Nat.add(Nat.add(da, db), Nat.add(a2, b2)) == Nat.add(a, b) : Nat}

def add.hom(a, b, da, a2, db, b2, ha, hb):
  %ha : {Nat.add(Nat.add(da, db), Nat.add(a2, b2)) == Nat.add(_, b) : Nat}
  %hb : {Nat.add(Nat.add(da, db), Nat.add(a2, b2)) == Nat.add(Nat.add(da, a2), _) : Nat}
  add.swap4(da, db, a2, b2)

law eq.G:
  for +d: Nat
  for +g: Gram
  for G: Gram
  for +y: String
  {Nat.add(sG(True{}, d, g, G, y), sG(False{}, 1n+d, g, G, y)) == sG(False{}, d, g, G, y) : Nat}

def eq.G(d, g, G, y):
  match G:
    case GNil{}:
      {==}
    case GCon{k, +r, +t}:
      add.hom(wt(False{}, d, g, r, y), sG(False{}, d, g, t, y), wt(True{}, d, g, r, y), wt(False{}, 1n+d, g, r, y), sG(True{}, d, g, t, y), sG(False{}, 1n+d, g, t, y), key.eq(sem(d, g, r, y, ""), sem(1n+d, g, r, y, ""), mono(d, g, r, y, "")), eq.G(d, g, t, y))

law eq.P:
  for +d: Nat
  for +g: Gram
  for x: String
  for +pre: String
  {Nat.add(sP(True{}, d, g, x, pre), sP(False{}, 1n+d, g, x, pre)) == sP(False{}, d, g, x, pre) : Nat}

def eq.P(d, g, x, pre):
  match x:
    case SNil{}:
      eq.G(d, g, g, pre)
    case SCon{+h, +t}:
      add.hom(sG(False{}, d, g, g, pre), sP(False{}, d, g, t, pre ++ SCon{h, SNil{}}), sG(True{}, d, g, g, pre), sG(False{}, 1n+d, g, g, pre), sP(True{}, d, g, t, pre ++ SCon{h, SNil{}}), sP(False{}, 1n+d, g, t, pre ++ SCon{h, SNil{}}), eq.G(d, g, g, pre), eq.P(d, g, t, pre ++ SCon{h, SNil{}}))

law eq.S:
  for +d: Nat
  for +g: Gram
  for s: String
  {Nat.add(sS(True{}, d, g, s), sS(False{}, 1n+d, g, s)) == sS(False{}, d, g, s) : Nat}

def eq.S(d, g, s):
  match s:
    case SNil{}:
      eq.P(d, g, SNil{}, "")
    case SCon{+h, +t}:
      add.hom(sP(False{}, d, g, SCon{h, t}, ""), sS(False{}, d, g, t), sP(True{}, d, g, SCon{h, t}, ""), sP(False{}, 1n+d, g, SCon{h, t}, ""), sS(True{}, d, g, t), sS(False{}, 1n+d, g, t), eq.P(d, g, SCon{h, t}, ""), eq.S(d, g, t))

law le.step:
  for b: Nat
  for c: Nat
  for h: T(Nat.is_le(b, c))
  T(Nat.is_le(b, 1n+c))

def le.step(b, c, h):
  match b c:
    case 0n _:
      {==}
    case 1n+p 0n:
      false.elim(T(Nat.is_le(1n+p, 1n)), h)
    case 1n+p 1n+q:
      le.step(p, q, h)

law le.add.z:
  for +c: Nat
  for +b: Nat
  for +c2: Nat
  for h: T(Nat.is_le(b, c2))
  T(Nat.is_le(b, Nat.add(c, c2)))

def le.add.z(c, b, c2, h):
  match c:
    case 0n:
      h
    case 1n+q:
      le.step(b, Nat.add(q, c2), le.add.z(q, b, c2, h))

law le.add:
  for a: Nat
  for c: Nat
  for +b: Nat
  for +c2: Nat
  for h1: T(Nat.is_le(a, c))
  for h2: T(Nat.is_le(b, c2))
  T(Nat.is_le(Nat.add(a, b), Nat.add(c, c2)))

def le.add(a, c, b, c2, h1, h2):
  match a c:
    case 0n 0n:
      h2
    case 0n 1n+q:
      le.add.z(1n+q, b, c2, h2)
    case 1n+p 0n:
      false.elim(T(Nat.is_le(1n+Nat.add(p, b), c2)), h1)
    case 1n+p 1n+q:
      le.add(p, q, b, c2, h1, h2)

law le.bv:
  for a: Bool
  T(Nat.is_le(bv(a), 1n))

def le.bv(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law le.G:
  for +d: Nat
  for +g: Gram
  for G: Gram
  for +y: String
  T(Nat.is_le(sG(False{}, d, g, G, y), capG(G)))

def le.G(d, g, G, y):
  match G:
    case GNil{}:
      {==}
    case GCon{k, +r, +t}:
      le.add(bv(sem(d, g, r, y, "")), 1n, sG(False{}, d, g, t, y), capG(t), le.bv(sem(d, g, r, y, "")), le.G(d, g, t, y))

law le.P:
  for +d: Nat
  for +g: Gram
  for x: String
  for +pre: String
  T(Nat.is_le(sP(False{}, d, g, x, pre), capP(capG(g), x)))

def le.P(d, g, x, pre):
  match x:
    case SNil{}:
      le.G(d, g, g, pre)
    case SCon{+h, +t}:
      le.add(sG(False{}, d, g, g, pre), capG(g), sP(False{}, d, g, t, pre ++ SCon{h, SNil{}}), capP(capG(g), t), le.G(d, g, g, pre), le.P(d, g, t, pre ++ SCon{h, SNil{}}))

law le.S:
  for +d: Nat
  for +g: Gram
  for s: String
  T(Nat.is_le(sS(False{}, d, g, s), bound(g, s)))

def le.S(d, g, s):
  match s:
    case SNil{}:
      le.P(d, g, SNil{}, "")
    case SCon{+h, +t}:
      le.add(sP(False{}, d, g, SCon{h, t}, ""), capP(capG(g), SCon{h, t}), sS(False{}, d, g, t), bound(g, t), le.P(d, g, SCon{h, t}, ""), le.S(d, g, t))

law ex.P.head:
  for +e: Nat
  for +g: Gram
  for v: String
  for +pre: String
  for h: {sP(True{}, e, g, v, pre) == 0n : Nat}
  {sG(True{}, e, g, g, pre) == 0n : Nat}

def ex.P.head(e, g, v, pre, h):
  match v:
    case SNil{}:
      h
    case SCon{c, t}:
      add.zero_l(sG(True{}, e, g, g, pre), sP(True{}, e, g, t, pre ++ SCon{c, SNil{}}), h)

law ex.P:
  for +e: Nat
  for +g: Gram
  for y: String
  for +v: String
  for +pre: String
  for h: {sP(True{}, e, g, y ++ v, pre) == 0n : Nat}
  {sG(True{}, e, g, g, pre ++ y) == 0n : Nat}

def ex.P(e, g, y, v, pre, h):
  match y:
    case SNil{}:
      %app.nil.sym(pre) : {sG(True{}, e, g, g, _) == 0n : Nat}
      ex.P.head(e, g, v, pre, h)
    case SCon{+c, +t}:
      %app.assoc(pre, SCon{c, SNil{}}, t) : {sG(True{}, e, g, g, _) == 0n : Nat}
      ex.P(e, g, t, v, pre ++ SCon{c, SNil{}}, add.zero_r(sG(True{}, e, g, g, pre), sP(True{}, e, g, t ++ v, pre ++ SCon{c, SNil{}}), h))

law ex.S.head:
  for +e: Nat
  for +g: Gram
  for s: String
  for h: {sS(True{}, e, g, s) == 0n : Nat}
  {sP(True{}, e, g, s, "") == 0n : Nat}

def ex.S.head(e, g, s, h):
  match s:
    case SNil{}:
      h
    case SCon{+c, +t}:
      add.zero_l(sP(True{}, e, g, SCon{c, t}, ""), sS(True{}, e, g, t), h)

law ex.S:
  for +e: Nat
  for +g: Gram
  for u: String
  for +y: String
  for +v: String
  for h: {sS(True{}, e, g, u ++ (y ++ v)) == 0n : Nat}
  {sG(True{}, e, g, g, y) == 0n : Nat}

def ex.S(e, g, u, y, v, h):
  match u:
    case SNil{}:
      ex.P(e, g, y, v, "", ex.S.head(e, g, y ++ v, h))
    case SCon{+c, +t}:
      ex.S(e, g, t, y, v, add.zero_r(sP(True{}, e, g, SCon{c, t ++ (y ++ v)}, ""), sS(True{}, e, g, t ++ (y ++ v)), h))

law hs.tr:
  for -e: Nat
  for -g: Gram
  for -S: String
  for -a: String
  for hs: {sS(True{}, e, g, S) == 0n : Nat}
  for h: {a == S : String}
  {sS(True{}, e, g, a) == 0n : Nat}

def hs.tr(e, g, S, a, hs, h):
  %Equal.sym(String, a, S, h) : {sS(True{}, e, g, _) == 0n : Nat}
  hs

law xv.eq:
  for a: Bool
  for b: Bool
  for h: {xv(a, b) == 0n : Nat}
  {a == b : Bool}

def xv.eq(a, b, h):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({False{} == True{} : Bool}, succ.empty(0n, h))
    case True{} False{}:
      absurd({True{} == False{} : Bool}, succ.empty(0n, h))
    case True{} True{}:
      {==}

law xv.refl:
  for a: Bool
  {xv(a, a) == 0n : Nat}

def xv.refl(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law xv.same:
  for a: Bool
  for -b: Bool
  for h: {a == b : Bool}
  {xv(a, b) == 0n : Nat}

def xv.same(a, b, h):
  %h : {xv(a, _) == 0n : Nat}
  xv.refl(a)

law cong.then:
  for -a: Bool
  for -a2: Bool
  for -b: Bool
  for -b2: Bool
  for h1: {a == a2 : Bool}
  for h2: {b == b2 : Bool}
  {then(a, u => b) == then(a2, u => b2) : Bool}

def cong.then(a, a2, b, b2, h1, h2):
  %h1 : {then(a, u => b) == then(_, u => b2) : Bool}
  %h2 : {then(a, u => b) == then(a, u => _) : Bool}
  {==}

law cong.or:
  for -a: Bool
  for -a2: Bool
  for -b: Bool
  for -b2: Bool
  for h1: {a == a2 : Bool}
  for h2: {b == b2 : Bool}
  {orelse(a, u => b) == orelse(a2, u => b2) : Bool}

def cong.or(a, a2, b, b2, h1, h2):
  %h1 : {orelse(a, u => b) == orelse(_, u => b2) : Bool}
  %h2 : {orelse(a, u => b) == orelse(a, u => _) : Bool}
  {==}

law sem.bad:
  for d: Nat
  for -g: Gram
  for -x: String
  for -p: String
  {sem(d, g, Bad{}, x, p) == False{} : Bool}

def sem.bad(d, g, x, p):
  match d:
    case 0n:
      {==}
    case 1n+e:
      {==}

law sem.alt:
  for d: Nat
  for -g: Gram
  for -a: R
  for -b: R
  for -x: String
  for -p: String
  {orelse(sem(d, g, a, x, ""), u => sem(d, g, b, x, "")) == sem(d, g, Alt{a, b}, x, p) : Bool}

def sem.alt(d, g, a, b, x, p):
  match d:
    case 0n:
      {==}
    case 1n+e:
      {==}

law cong.pick:
  for +e: Nat
  for -g: Gram
  for c: Bool
  for -r: R
  for -rest: R
  for -x: String
  for h1: {sem(e, g, r, x, "") == sem(1n+e, g, r, x, "") : Bool}
  for h2: {sem(e, g, rest, x, "") == sem(1n+e, g, rest, x, "") : Bool}
  {sem(e, g, lk.pick(c, r, rest), x, "") == sem(1n+e, g, lk.pick(c, r, rest), x, "") : Bool}

def cong.pick(e, g, c, r, rest, x, h1, h2):
  match c:
    case False{}:
      h2
    case True{}:
      %sem.alt(e, g, r, rest, x, "") : {_ == sem(1n+e, g, Alt{r, rest}, x, "") : Bool}
      cong.or(sem(e, g, r, x, ""), sem(1n+e, g, r, x, ""), sem(e, g, rest, x, ""), sem(1n+e, g, rest, x, ""), h1, h2)

law cong.lk:
  for +e: Nat
  for +g: Gram
  for G: Gram
  for +n: String
  for +x: String
  for +h: {sG(True{}, e, g, G, x) == 0n : Nat}
  {sem(e, g, lk(G, n), x, "") == sem(1n+e, g, lk(G, n), x, "") : Bool}

def cong.lk(e, g, G, n, x, h):
  match G:
    case GNil{}:
      sem.bad(e, g, x, "")
    case GCon{k, +r, +t}:
      cong.pick(e, g, String.eq(String.to_lower(k), String.to_lower(n)), r, lk(t, n), x, xv.eq(sem(e, g, r, x, ""), sem(1n+e, g, r, x, ""), add.zero_l(wt(True{}, e, g, r, x), sG(True{}, e, g, t, x), h)), cong.lk(e, g, t, n, x, add.zero_r(wt(True{}, e, g, r, x), sG(True{}, e, g, t, x), h)))

law cong:
  for +e: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, e, g, S) == 0n : Nat}
  for r: R
  for +x: String
  for +p: String
  for +u: String
  for +v: String
  for +h: {u ++ ((p ++ x) ++ v) == S : String}
  {sem(1n+e, g, r, x, p) == sem(2n+e, g, r, x, p) : Bool}

def cong(e, g, S, hs, r, x, p, u, v, h):
  match r:
    case Emp{}:
      {==}
    case Bad{}:
      {==}
    case Lit{c}:
      match x:
        case SNil{}:
          {==}
        case SCon{hd, t}:
          match t:
            case SNil{}:
              {==}
            case SCon{h2, t2}:
              {==}
    case Rng{lo, hi}:
      match x:
        case SNil{}:
          {==}
        case SCon{hd, t}:
          match t:
            case SNil{}:
              {==}
            case SCon{h2, t2}:
              {==}
    case Cat{+a, +b}:
      match x:
        case SNil{}:
          cong.then(sem(1n+e, g, a, p, ""), sem(2n+e, g, a, p, ""), sem(1n+e, g, b, SNil{}, ""), sem(2n+e, g, b, SNil{}, ""), cong(e, g, S, hs, a, p, "", u, SNil{} ++ v, sub.left(u, p, SNil{}, v, S, h)), cong(e, g, S, hs, b, SNil{}, "", u ++ p, v, sub.right(u, p, SNil{}, v, S, h)))
        case SCon{+hd, +t}:
          cong.or(then(sem(1n+e, g, a, p, ""), u => sem(1n+e, g, b, SCon{hd, t}, "")), then(sem(2n+e, g, a, p, ""), u => sem(2n+e, g, b, SCon{hd, t}, "")), sem(1n+e, g, Cat{a, b}, t, p ++ SCon{hd, SNil{}}), sem(2n+e, g, Cat{a, b}, t, p ++ SCon{hd, SNil{}}), cong.then(sem(1n+e, g, a, p, ""), sem(2n+e, g, a, p, ""), sem(1n+e, g, b, SCon{hd, t}, ""), sem(2n+e, g, b, SCon{hd, t}, ""), cong(e, g, S, hs, a, p, "", u, SCon{hd, t} ++ v, sub.left(u, p, SCon{hd, t}, v, S, h)), cong(e, g, S, hs, b, SCon{hd, t}, "", u ++ p, v, sub.right(u, p, SCon{hd, t}, v, S, h))), cong(e, g, S, hs, Cat{a, b}, t, p ++ SCon{hd, SNil{}}, u, v, sub.snoc(u, p, hd, t, v, S, h)))
    case Alt{+a, +b}:
      cong.or(sem(1n+e, g, a, x, ""), sem(2n+e, g, a, x, ""), sem(1n+e, g, b, x, ""), sem(2n+e, g, b, x, ""), cong(e, g, S, hs, a, x, "", u ++ p, v, sub.right(u, p, x, v, S, h)), cong(e, g, S, hs, b, x, "", u ++ p, v, sub.right(u, p, x, v, S, h)))
    case Star{+a}:
      match x:
        case SNil{}:
          cong.or(String.is_empty(p), String.is_empty(p), sem(1n+e, g, a, p, ""), sem(2n+e, g, a, p, ""), {==}, cong(e, g, S, hs, a, p, "", u, SNil{} ++ v, sub.left(u, p, SNil{}, v, S, h)))
        case SCon{+hd, +t}:
          cong.or(then(sem(1n+e, g, a, p, ""), u => sem(1n+e, g, Star{a}, t, SCon{hd, SNil{}})), then(sem(2n+e, g, a, p, ""), u => sem(2n+e, g, Star{a}, t, SCon{hd, SNil{}})), sem(1n+e, g, Star{a}, t, p ++ SCon{hd, SNil{}}), sem(2n+e, g, Star{a}, t, p ++ SCon{hd, SNil{}}), cong.then(sem(1n+e, g, a, p, ""), sem(2n+e, g, a, p, ""), sem(1n+e, g, Star{a}, t, SCon{hd, SNil{}}), sem(2n+e, g, Star{a}, t, SCon{hd, SNil{}}), cong(e, g, S, hs, a, p, "", u, SCon{hd, t} ++ v, sub.left(u, p, SCon{hd, t}, v, S, h)), cong(e, g, S, hs, Star{a}, t, SCon{hd, SNil{}}, u ++ p, v, sub.right(u, p, SCon{hd, t}, v, S, h))), cong(e, g, S, hs, Star{a}, t, p ++ SCon{hd, SNil{}}, u, v, sub.snoc(u, p, hd, t, v, S, h)))
    case Ref{+n}:
      cong.lk(e, g, g, n, x, ex.S(e, g, u ++ p, x, v, hs.tr(e, g, S, (u ++ p) ++ (x ++ v), hs, sub.right(u, p, x, v, S, h))))

# ---- once nothing changes, nothing ever changes ----

law persist.G:
  for +e: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, e, g, S) == 0n : Nat}
  for G: Gram
  for +x: String
  for +u: String
  for +v: String
  for +h: {u ++ (x ++ v) == S : String}
  {sG(True{}, 1n+e, g, G, x) == 0n : Nat}

def persist.G(e, g, S, hs, G, x, u, v, h):
  match G:
    case GNil{}:
      {==}
    case GCon{k, +r, +t}:
      add.zeros(wt(True{}, 1n+e, g, r, x), sG(True{}, 1n+e, g, t, x), xv.same(sem(1n+e, g, r, x, ""), sem(2n+e, g, r, x, ""), cong(e, g, S, hs, r, x, "", u, v, h)), persist.G(e, g, S, hs, t, x, u, v, h))

law persist.P:
  for +e: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, e, g, S) == 0n : Nat}
  for x: String
  for +pre: String
  for +u: String
  for +v: String
  for +h: {u ++ ((pre ++ x) ++ v) == S : String}
  {sP(True{}, 1n+e, g, x, pre) == 0n : Nat}

def persist.P(e, g, S, hs, x, pre, u, v, h):
  match x:
    case SNil{}:
      persist.G(e, g, S, hs, g, pre, u, v, sub.left(u, pre, SNil{}, v, S, h))
    case SCon{+c, +t}:
      add.zeros(sG(True{}, 1n+e, g, g, pre), sP(True{}, 1n+e, g, t, pre ++ SCon{c, SNil{}}), persist.G(e, g, S, hs, g, pre, u, SCon{c, t} ++ v, sub.left(u, pre, SCon{c, t}, v, S, h)), persist.P(e, g, S, hs, t, pre ++ SCon{c, SNil{}}, u, v, sub.snoc(u, pre, c, t, v, S, h)))

law persist.S:
  for +e: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, e, g, S) == 0n : Nat}
  for s: String
  for +u: String
  for +v: String
  for +h: {u ++ (s ++ v) == S : String}
  {sS(True{}, 1n+e, g, s) == 0n : Nat}

def persist.S(e, g, S, hs, s, u, v, h):
  match s:
    case SNil{}:
      persist.P(e, g, S, hs, SNil{}, "", u, v, h)
    case SCon{+c, +t}:
      add.zeros(sP(True{}, 1n+e, g, SCon{c, t}, ""), sS(True{}, 1n+e, g, t), persist.P(e, g, S, hs, SCon{c, t}, "", u, v, h), persist.S(e, g, S, hs, t, u ++ SCon{c, SNil{}}, v, sub.right(u, SCon{c, SNil{}}, t, v, S, h)))

law persist:
  for +e: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, e, g, S) == 0n : Nat}
  {sS(True{}, 1n+e, g, S) == 0n : Nat}

def persist(e, g, S, hs):
  persist.S(e, g, S, hs, S, "", "", app.nil(S))

law persist.add:
  for +k: Nat
  for +d: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, d, g, S) == 0n : Nat}
  {sS(True{}, Nat.add(k, d), g, S) == 0n : Nat}

def persist.add(k, d, g, S, hs):
  match k:
    case 0n:
      hs
    case 1n+j:
      persist(Nat.add(j, d), g, S, persist.add(j, d, g, S, hs))

# ---- the count of unmatched pairs can only fall so many times ----

law le.zero:
  for a: Nat
  for h: T(Nat.is_le(a, 0n))
  {a == 0n : Nat}

def le.zero(a, h):
  match a:
    case 0n:
      {==}
    case 1n+p:
      false.elim({1n+p == 0n : Nat}, h)

law le.pred:
  for x: Nat
  for c: Nat
  for h: T(Nat.is_le(1n+x, c))
  T(Nat.is_le(x, c))

def le.pred(x, c, h):
  match c:
    case 0n:
      false.elim(T(Nat.is_le(x, 0n)), h)
    case 1n+q:
      le.step(x, q, h)

law le.add_left:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for h: T(Nat.is_le(Nat.add(a, b), c))
  T(Nat.is_le(b, c))

def le.add_left(a, b, c, h):
  match a:
    case 0n:
      h
    case 1n+p:
      le.add_left(p, b, c, le.pred(Nat.add(p, b), c, h))

law settle.step.go:
  for -t: Nat
  for -f: Nat
  for -f1: Nat
  for -j: Nat
  for -m: Nat
  for e1: {Nat.add(t, f1) == f : Nat}
  for hm: {t == 1n+m : Nat}
  for h: T(Nat.is_le(f, 1n+j))
  T(Nat.is_le(1n+Nat.add(m, f1), 1n+j))

def settle.step.go(t, f, f1, j, m, e1, hm, h):
  %hm : {Nat.is_le(Nat.add(_, f1), 1n+j) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(t, f1), f, e1) : {Nat.is_le(_, 1n+j) == True{} : Bool}
  h

law settle.step:
  for -t: Nat
  for -f: Nat
  for +f1: Nat
  for +j: Nat
  for +m: Nat
  for e1: {Nat.add(t, f1) == f : Nat}
  for hm: {t == 1n+m : Nat}
  for h: T(Nat.is_le(f, 1n+j))
  T(Nat.is_le(f1, j))

def settle.step(t, f, f1, j, m, e1, hm, h):
  le.add_left(m, f1, j, settle.step.go(t, f, f1, j, m, e1, hm, h))

law settle.fin:
  for -j: Nat
  for -d: Nat
  for -g: Gram
  for -S: String
  for +j2: Nat
  for ih: {sS(True{}, Nat.add(j2, 1n+d), g, S) == 0n : Nat}
  {sS(True{}, 1n+Nat.add(j2, d), g, S) == 0n : Nat}

def settle.fin(j, d, g, S, j2, ih):
  %Equal.sym(Nat, 1n+Nat.add(j2, d), Nat.add(j2, 1n+d), add.succ(j2, d)) : {sS(True{}, _, g, S) == 0n : Nat}
  ih

def nat.split(v: Nat, -C: Type, ez: {v == 0n : Nat} -> C, es: @m: Nat -> {v == 1n+m : Nat} -> C) -> C:
  match v:
    case 0n:
      ez({==})
    case 1n+p:
      es(p, {==})

law settle:
  for +k: Nat
  for +d: Nat
  for +g: Gram
  for +S: String
  for h: T(Nat.is_le(sS(False{}, d, g, S), k))
  {sS(True{}, Nat.add(k, d), g, S) == 0n : Nat}

def settle(k, d, g, S, h):
  match k:
    case 0n:
      add.zero_l(sS(True{}, d, g, S), sS(False{}, 1n+d, g, S), Equal.trans(Nat, Nat.add(sS(True{}, d, g, S), sS(False{}, 1n+d, g, S)), sS(False{}, d, g, S), 0n, eq.S(d, g, S), le.zero(sS(False{}, d, g, S), h)))
    case 1n+j:
      nat.split(sS(True{}, d, g, S), {sS(True{}, 1n+Nat.add(j, d), g, S) == 0n : Nat}, +hz => persist.add(1n+j, d, g, S, hz), +m => hm => settle.fin(j, d, g, S, j, settle(j, 1n+d, g, S, settle.step(sS(True{}, d, g, S), sS(False{}, d, g, S), sS(False{}, 1n+d, g, S), j, m, eq.S(d, g, S), hm, h))))

law settled:
  for +g: Gram
  for +S: String
  {sS(True{}, bound(g, S), g, S) == 0n : Nat}

def settled(g, S):
  %add.zero(bound(g, S)) : {sS(True{}, _, g, S) == 0n : Nat}
  settle(bound(g, S), 0n, g, S, le.S(0n, g, S))

# ---- `bound` is enough: `full` is the limit of `limit` ----

law stable:
  for +k: Nat
  for +D: Nat
  for +g: Gram
  for +S: String
  for +hs: {sS(True{}, D, g, S) == 0n : Nat}
  for +r: R
  for +x: String
  for +p: String
  for +u: String
  for +v: String
  for +h: {u ++ ((p ++ x) ++ v) == S : String}
  {sem(1n+Nat.add(k, D), g, r, x, p) == sem(1n+D, g, r, x, p) : Bool}

def stable(k, D, g, S, hs, r, x, p, u, v, h):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Bool, sem(2n+Nat.add(j, D), g, r, x, p), sem(1n+Nat.add(j, D), g, r, x, p), sem(1n+D, g, r, x, p), Equal.sym(Bool, sem(1n+Nat.add(j, D), g, r, x, p), sem(2n+Nat.add(j, D), g, r, x, p), cong(Nat.add(j, D), g, S, persist.add(j, D, g, S, hs), r, x, p, u, v, h)), stable(j, D, g, S, hs, r, x, p, u, v, h))

law le.sub:
  for +d: Nat
  for +b: Nat
  for h: T(Nat.is_le(d, b))
  {b == Nat.add(Nat.sub(b, d), d) : Nat}

def le.sub(d, b, h):
  match d b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Nat, Nat.add(1n+q, 0n), 1n+q, add.zero(1n+q))
    case 1n+p 0n:
      false.elim({0n == Nat.add(0n, 1n+p) : Nat}, h)
    case 1n+p 1n+q:
      %add.succ(Nat.sub(q, p), p) : {1n+q == _ : Nat}
      %le.sub(p, q, h) : {1n+q == 1n+_ : Nat}
      {==}

law true.not_false:
  for h: {True{} == False{} : Bool}
  Empty

def true.not_false(h):
  false.empty(Equal.sym(Bool, True{}, False{}, h))

law le.flip:
  for d: Nat
  for b: Nat
  for h: {Nat.is_le(d, b) == False{} : Bool}
  T(Nat.is_le(b, d))

def le.flip(d, b, h):
  match d b:
    case 0n 0n:
      absurd(T(Nat.is_le(0n, 0n)), true.not_false(h))
    case 0n 1n+q:
      absurd(T(Nat.is_le(1n+q, 0n)), true.not_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le.flip(p, q, h)

def bool.split(c: Bool, -C: Type, t: {c == True{} : Bool} -> C, f: {c == False{} : Bool} -> C) -> C:
  match c:
    case False{}:
      f({==})
    case True{}:
      t({==})

law complete.up:
  for +d: Nat
  for +b: Nat
  for +g: Gram
  for +r: R
  for +y: String
  for +c: T(Nat.is_le(d, b))
  for +hm: T(sem(d, g, r, y, ""))
  T(sem(b, g, r, y, ""))

def complete.up(d, b, g, r, y, c, hm):
  %Equal.sym(Nat, b, Nat.add(Nat.sub(b, d), d), le.sub(d, b, c)) : {sem(_, g, r, y, "") == True{} : Bool}
  mono.add(Nat.sub(b, d), d, g, r, y, "", hm)

law complete.down:
  for +d: Nat
  for +g: Gram
  for +S: String
  for +r: R
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == S : String}
  for +c: {Nat.is_le(d, 1n+bound(g, S)) == False{} : Bool}
  for +hm: T(sem(d, g, r, y, ""))
  T(sem(1n+bound(g, S), g, r, y, ""))

def complete.down(d, g, S, r, y, u, v, h, c, hm):
  %stable(Nat.sub(d, 1n+bound(g, S)), bound(g, S), g, S, settled(g, S), r, y, "", u, v, h) : {_ == True{} : Bool}
  %Equal.sym(Nat, 1n+Nat.add(Nat.sub(d, 1n+bound(g, S)), bound(g, S)), Nat.add(Nat.sub(d, 1n+bound(g, S)), 1n+bound(g, S)), add.succ(Nat.sub(d, 1n+bound(g, S)), bound(g, S))) : {sem(_, g, r, y, "") == True{} : Bool}
  %le.sub(1n+bound(g, S), d, le.flip(d, 1n+bound(g, S), c)) : {sem(_, g, r, y, "") == True{} : Bool}
  hm

law complete:
  for +d: Nat
  for +g: Gram
  for +S: String
  for +r: R
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == S : String}
  for +hm: T(sem(d, g, r, y, ""))
  T(sem(1n+bound(g, S), g, r, y, ""))

def complete(d, g, S, r, y, u, v, h, hm):
  bool.split(Nat.is_le(d, 1n+bound(g, S)), T(sem(1n+bound(g, S), g, r, y, "")), +c => complete.up(d, 1n+bound(g, S), g, r, y, c, hm), +c => complete.down(d, g, S, r, y, u, v, h, c, hm))

# ---- splitting and repeating, at a fixed fuel ----

law then.intro:
  for a: Bool
  for -b: Bool
  for ha: T(a)
  for hb: T(b)
  T(then(a, u => b))

def then.intro(a, b, ha, hb):
  match a:
    case False{}:
      false.elim(T(False{}), ha)
    case True{}:
      hb

law then.fst:
  for a: Bool
  for -b: Bool
  for h: T(then(a, u => b))
  T(a)

def then.fst(a, b, h):
  match a:
    case False{}:
      h
    case True{}:
      {==}

law then.snd:
  for a: Bool
  for -b: Bool
  for h: T(then(a, u => b))
  T(b)

def then.snd(a, b, h):
  match a:
    case False{}:
      false.elim(T(b), h)
    case True{}:
      h

law or.left:
  for a: Bool
  for -b: Bool
  for ha: T(a)
  T(orelse(a, u => b))

def or.left(a, b, ha):
  match a:
    case False{}:
      false.elim(T(b), ha)
    case True{}:
      {==}

law or.right:
  for a: Bool
  for -b: Bool
  for hb: T(b)
  T(orelse(a, u => b))

def or.right(a, b, hb):
  match a:
    case False{}:
      hb
    case True{}:
      {==}

def or.elim(a: Bool, -b: Bool, -C: Type, h: T(orelse(a, u => b)), f: T(a) -> C, k: T(b) -> C) -> C:
  match a:
    case False{}:
      k(h)
    case True{}:
      f({==})

law or.eq:
  for a: Bool
  for -b: Bool
  {orelse(a, u => b) == a || b : Bool}

def or.eq(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law tr.x:
  for -d: Nat
  for -g: Gram
  for -r: R
  for -x: String
  for -y: String
  for e: {x == y : String}
  for h: T(sem(d, g, r, x, ""))
  T(sem(d, g, r, y, ""))

def tr.x(d, g, r, x, y, e, h):
  %e : {sem(d, g, r, _, "") == True{} : Bool}
  h

law cat.intro:
  for +d: Nat
  for +g: Gram
  for +a: R
  for +b: R
  for s1: String
  for +s2: String
  for +p: String
  for h1: T(sem(d, g, a, p ++ s1, ""))
  for h2: T(sem(d, g, b, s2, ""))
  T(sem(d, g, Cat{a, b}, s1 ++ s2, p))

def cat.intro(d, g, a, b, s1, s2, p, h1, h2):
  match d:
    case 0n:
      false.elim(T(False{}), h1)
    case 1n+e:
      match s1:
        case SNil{}:
          match s2:
            case SNil{}:
              then.intro(sem(d, g, a, p, ""), sem(d, g, b, SNil{}, ""), tr.x(d, g, a, p ++ "", p, app.nil(p), h1), h2)
            case SCon{c, t}:
              or.left(then(sem(d, g, a, p, ""), u => sem(d, g, b, SCon{c, t}, "")), sem(d, g, Cat{a, b}, t, p ++ SCon{c, SNil{}}), then.intro(sem(d, g, a, p, ""), sem(d, g, b, SCon{c, t}, ""), tr.x(d, g, a, p ++ "", p, app.nil(p), h1), h2))
        case SCon{+c, +t}:
          or.right(then(sem(d, g, a, p, ""), u => sem(d, g, b, SCon{c, t ++ s2}, "")), sem(d, g, Cat{a, b}, t ++ s2, p ++ SCon{c, SNil{}}), cat.intro(d, g, a, b, t, s2, p ++ SCon{c, SNil{}}, tr.x(d, g, a, p ++ SCon{c, t}, (p ++ SCon{c, SNil{}}) ++ t, app.assoc.sym(p, SCon{c, SNil{}}, t), h1), h2))

law cat.elim.eq:
  for -c: Char
  for -s1: String
  for -s2: String
  for -t: String
  for e: {s1 ++ s2 == t : String}
  {SCon{c, s1 ++ s2} == SCon{c, t} : String}

def cat.elim.eq(c, s1, s2, t, e):
  %e : {SCon{c, s1 ++ s2} == SCon{c, _} : String}
  {==}

def CatW(d: Nat, g: Gram, a: R, b: R, x: String, p: String) -> Type:
  &s1: String -> &s2: String -> {s1 ++ s2 == x : String} & T(sem(d, g, a, p ++ s1, "")) & T(sem(d, g, b, s2, ""))

law cat.elim.k:
  for -d: Nat
  for -g: Gram
  for -a: R
  for -b: R
  for +c: Char
  for -t: String
  for +p: String
  for w: CatW(d, g, a, b, t, p ++ SCon{c, SNil{}})
  CatW(d, g, a, b, SCon{c, t}, p)

def cat.elim.k(d, g, a, b, c, t, p, w):
  match w:
    case (+s1, s2, e, ha, hb):
      (SCon{c, s1}, s2, cat.elim.eq(c, s1, s2, t, e), tr.x(d, g, a, (p ++ SCon{c, SNil{}}) ++ s1, p ++ SCon{c, s1}, app.assoc(p, SCon{c, SNil{}}, s1), ha), hb)

law cat.elim:
  for +d: Nat
  for +g: Gram
  for +a: R
  for +b: R
  for x: String
  for +p: String
  for +h: T(sem(d, g, Cat{a, b}, x, p))
  CatW(d, g, a, b, x, p)

def cat.elim(d, g, a, b, x, p, h):
  match d:
    case 0n:
      false.elim(CatW(0n, g, a, b, x, p), h)
    case 1n+e:
      match x:
        case SNil{}:
          ("", "", {==}, tr.x(d, g, a, p, p ++ "", app.nil.sym(p), then.fst(sem(d, g, a, p, ""), sem(d, g, b, SNil{}, ""), h)), then.snd(sem(d, g, a, p, ""), sem(d, g, b, SNil{}, ""), h))
        case SCon{+c, +t}:
          or.elim(then(sem(d, g, a, p, ""), u => sem(d, g, b, SCon{c, t}, "")), sem(d, g, Cat{a, b}, t, p ++ SCon{c, SNil{}}), CatW(d, g, a, b, SCon{c, t}, p), h, +hl => ("", SCon{c, t}, {==}, tr.x(d, g, a, p, p ++ "", app.nil.sym(p), then.fst(sem(d, g, a, p, ""), sem(d, g, b, SCon{c, t}, ""), hl)), then.snd(sem(d, g, a, p, ""), sem(d, g, b, SCon{c, t}, ""), hl)), hr => cat.elim.k(d, g, a, b, c, t, p, cat.elim(d, g, a, b, t, p ++ SCon{c, SNil{}}, hr)))

law star.step:
  for +d: Nat
  for +g: Gram
  for +a: R
  for t: String
  for +s2: String
  for +p: String
  for h1: T(sem(d, g, a, p ++ t, ""))
  for h2: T(sem(d, g, Star{a}, s2, ""))
  T(sem(d, g, Star{a}, t ++ s2, p))

def star.step(d, g, a, t, s2, p, h1, h2):
  match d:
    case 0n:
      false.elim(T(False{}), h1)
    case 1n+e:
      match t:
        case SNil{}:
          match s2:
            case SNil{}:
              or.right(String.is_empty(p), sem(d, g, a, p, ""), tr.x(d, g, a, p ++ "", p, app.nil(p), h1))
            case SCon{c, t2}:
              or.left(then(sem(d, g, a, p, ""), u => sem(d, g, Star{a}, t2, SCon{c, SNil{}})), sem(d, g, Star{a}, t2, p ++ SCon{c, SNil{}}), then.intro(sem(d, g, a, p, ""), sem(d, g, Star{a}, t2, SCon{c, SNil{}}), tr.x(d, g, a, p ++ "", p, app.nil(p), h1), or.elim(then(sem(d, g, a, "", ""), u => sem(d, g, Star{a}, t2, SCon{c, SNil{}})), sem(d, g, Star{a}, t2, SCon{c, SNil{}}), T(sem(d, g, Star{a}, t2, SCon{c, SNil{}})), h2, hl => then.snd(sem(d, g, a, "", ""), sem(d, g, Star{a}, t2, SCon{c, SNil{}}), hl), hr => hr)))
        case SCon{+c, +t2}:
          or.right(then(sem(d, g, a, p, ""), u => sem(d, g, Star{a}, t2 ++ s2, SCon{c, SNil{}})), sem(d, g, Star{a}, t2 ++ s2, p ++ SCon{c, SNil{}}), star.step(d, g, a, t2, s2, p ++ SCon{c, SNil{}}, tr.x(d, g, a, p ++ SCon{c, t2}, (p ++ SCon{c, SNil{}}) ++ t2, app.assoc.sym(p, SCon{c, SNil{}}, t2), h1), h2))

law star.cons:
  for +d: Nat
  for +g: Gram
  for +a: R
  for s1: String
  for +s2: String
  for h1: T(sem(d, g, a, s1, ""))
  for h2: T(sem(d, g, Star{a}, s2, ""))
  T(sem(d, g, Star{a}, s1 ++ s2, ""))

def star.cons(d, g, a, s1, s2, h1, h2):
  match d:
    case 0n:
      false.elim(T(False{}), h1)
    case 1n+e:
      match s1:
        case SNil{}:
          h2
        case SCon{+c, +t}:
          or.right(then(sem(d, g, a, "", ""), u => sem(d, g, Star{a}, t ++ s2, SCon{c, SNil{}})), sem(d, g, Star{a}, t ++ s2, SCon{c, SNil{}}), star.step(d, g, a, t, s2, SCon{c, SNil{}}, h1, h2))

law seq2.intro:
  for +d: Nat
  for +g: Gram
  for +a: R
  for +b: R
  for s1: String
  for +s2: String
  for h1: T(sem(d, g, a, s1, ""))
  for h2: T(sem(d, g, b, s2, ""))
  T(sem(d, g, Cat{a, Cat{b, Emp{}}}, s1 ++ s2, ""))

def seq2.intro(d, g, a, b, s1, s2, h1, h2):
  match d:
    case 0n:
      false.elim(T(False{}), h1)
    case 1n+e:
      cat.intro(d, g, a, Cat{b, Emp{}}, s1, s2, "", h1, tr.x(d, g, Cat{b, Emp{}}, s2 ++ "", s2, app.nil(s2), cat.intro(d, g, b, Emp{}, s2, "", "", h2, {==})))

law emp.nil:
  for d: Nat
  for -g: Gram
  for v: String
  for h: T(sem(d, g, Emp{}, v, ""))
  {v == "" : String}

def emp.nil(d, g, v, h):
  match d:
    case 0n:
      false.elim({v == "" : String}, h)
    case 1n+e:
      match v:
        case SNil{}:
          {==}
        case SCon{c, t}:
          false.elim({SCon{c, t} == "" : String}, h)

def Seq2W(d: Nat, g: Gram, a: R, b: R, s: String) -> Type:
  &s1: String -> &s2: String -> {s1 ++ s2 == s : String} & T(sem(d, g, a, s1, "")) & T(sem(d, g, b, s2, ""))

law seq2.eq:
  for x: String
  for -y: String
  for -s2: String
  for e2: {x ++ y == s2 : String}
  for ey: {y == "" : String}
  {s2 == x : String}

def seq2.eq(x, y, s2, e2, ey):
  %e2 : {_ == x : String}
  %Equal.sym(String, y, "", ey) : {x ++ _ == x : String}
  app.nil(x)

law seq2.eq2:
  for -s1: String
  for -s2: String
  for -s: String
  for x: String
  for -y: String
  for e1: {s1 ++ s2 == s : String}
  for e2: {x ++ y == s2 : String}
  for ey: {y == "" : String}
  {s1 ++ x == s : String}

def seq2.eq2(s1, s2, s, x, y, e1, e2, ey):
  %seq2.eq(x, y, s2, e2, ey) : {s1 ++ _ == s : String}
  e1

law seq2.k2:
  for +d: Nat
  for -g: Gram
  for -a: R
  for -b: R
  for -s: String
  for +s1: String
  for -s2: String
  for w: CatW(d, g, b, Emp{}, s2, "")
  for e1: {s1 ++ s2 == s : String}
  for ha: T(sem(d, g, a, s1, ""))
  Seq2W(d, g, a, b, s)

def seq2.k2(d, g, a, b, s, s1, s2, w, e1, ha):
  match w:
    case (+x, +y, e2, hx, hy):
      (s1, x, seq2.eq2(s1, s2, s, x, y, e1, e2, emp.nil(d, g, y, hy)), ha, hx)

law seq2.k1:
  for +d: Nat
  for +g: Gram
  for -a: R
  for +b: R
  for -s: String
  for w: CatW(d, g, a, Cat{b, Emp{}}, s, "")
  Seq2W(d, g, a, b, s)

def seq2.k1(d, g, a, b, s, w):
  match w:
    case (+s1, +s2, e1, ha, hc):
      seq2.k2(d, g, a, b, s, s1, s2, cat.elim(d, g, b, Emp{}, s2, "", hc), e1, ha)

law seq2.elim:
  for +d: Nat
  for +g: Gram
  for +a: R
  for +b: R
  for s: String
  for +h: T(sem(d, g, Cat{a, Cat{b, Emp{}}}, s, ""))
  Seq2W(d, g, a, b, s)

def seq2.elim(d, g, a, b, s, h):
  seq2.k1(d, g, a, b, s, cat.elim(d, g, a, Cat{b, Emp{}}, s, "", h))

def seq2.with(-d: Nat, -g: Gram, -a: R, -b: R, -s: String, w: Seq2W(d, g, a, b, s), -C: Type, k: @s1: String -> @s2: String -> {s1 ++ s2 == s : String} -> T(sem(d, g, a, s1, "")) -> T(sem(d, g, b, s2, "")) -> C) -> C:
  match w:
    case (s1, s2, e, h1, h2):
      k(s1, s2, e, h1, h2)

def exact(n: Nat, +r: R) -> R:
  match n:
    case 0n:
      Emp{}
    case 1n+m:
      Cat{r, Cat{exact(m, r), Emp{}}}

law star.intro:
  for +m: Nat
  for +d: Nat
  for +g: Gram
  for +a: R
  for +s: String
  for h: T(sem(d, g, exact(m, a), s, ""))
  T(sem(d, g, Star{a}, s, ""))

def star.intro(m, d, g, a, s, h):
  match m:
    case 0n:
      match d:
        case 0n:
          false.elim(T(False{}), h)
        case 1n+e:
          match s:
            case SNil{}:
              {==}
            case SCon{c, t}:
              false.elim(T(sem(d, g, Star{a}, SCon{c, t}, "")), h)
    case 1n+j:
      seq2.with(d, g, a, exact(j, a), s, seq2.elim(d, g, a, exact(j, a), s, h), T(sem(d, g, Star{a}, s, "")), +s1 => +s2 => e => h1 => h2 => tr.x(d, g, Star{a}, s1 ++ s2, s, e, star.cons(d, g, a, s1, s2, h1, star.intro(j, d, g, a, s2, h2))))

def ExW(d: Nat, g: Gram, a: R, y: String) -> Type:
  &m: Nat -> T(sem(d, g, exact(m, a), y, ""))

law star.k1:
  for +d: Nat
  for +g: Gram
  for +a: R
  for +c: Char
  for +t: String
  for +p: String
  for ha: T(sem(d, g, a, p, ""))
  for w: ExW(d, g, a, SCon{c, t})
  ExW(d, g, a, p ++ SCon{c, t})

def star.k1(d, g, a, c, t, p, ha, w):
  match w:
    case (+m, hm):
      (1n+m, seq2.intro(d, g, a, exact(m, a), p, SCon{c, t}, ha, hm))

law star.k2:
  for -d: Nat
  for -g: Gram
  for -a: R
  for -c: Char
  for -t: String
  for +p: String
  for w: ExW(d, g, a, (p ++ SCon{c, SNil{}}) ++ t)
  ExW(d, g, a, p ++ SCon{c, t})

def star.k2(d, g, a, c, t, p, w):
  match w:
    case (+m, hm):
      (m, tr.x(d, g, exact(m, a), (p ++ SCon{c, SNil{}}) ++ t, p ++ SCon{c, t}, app.assoc(p, SCon{c, SNil{}}, t), hm))

law star.elim:
  for +d: Nat
  for +g: Gram
  for +a: R
  for x: String
  for +p: String
  for +h: T(sem(d, g, Star{a}, x, p))
  ExW(d, g, a, p ++ x)

def star.elim(d, g, a, x, p, h):
  match d:
    case 0n:
      false.elim(ExW(0n, g, a, p ++ x), h)
    case 1n+e:
      match x:
        case SNil{}:
          or.elim(String.is_empty(p), sem(d, g, a, p, ""), ExW(d, g, a, p ++ ""), h, hp => (0n, tr.x(d, g, Emp{}, p, p ++ "", app.nil.sym(p), hp)), ha => (1n, seq2.intro(d, g, a, Emp{}, p, "", ha, {==})))
        case SCon{+c, +t}:
          or.elim(then(sem(d, g, a, p, ""), u => sem(d, g, Star{a}, t, SCon{c, SNil{}})), sem(d, g, Star{a}, t, p ++ SCon{c, SNil{}}), ExW(d, g, a, p ++ SCon{c, t}), h, +hl => star.k1(d, g, a, c, t, p, then.fst(sem(d, g, a, p, ""), sem(d, g, Star{a}, t, SCon{c, SNil{}}), hl), star.elim(d, g, a, t, SCon{c, SNil{}}, then.snd(sem(d, g, a, p, ""), sem(d, g, Star{a}, t, SCon{c, SNil{}}), hl))), hr => star.k2(d, g, a, c, t, p, star.elim(d, g, a, t, p ++ SCon{c, SNil{}}, hr)))

law le0:
  for m: Nat
  T(Nat.is_le(0n, m))

def le0(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def atl(n: Nat, +r: R) -> R:
  match n:
    case 0n:
      Star{r}
    case 1n+m:
      Cat{r, Cat{atl(m, r), Emp{}}}

law atl.intro:
  for +n: Nat
  for +m: Nat
  for h: T(Nat.is_le(n, m))
  for +d: Nat
  for +g: Gram
  for +a: R
  for +s: String
  for hs: T(sem(d, g, exact(m, a), s, ""))
  T(sem(d, g, atl(n, a), s, ""))

def atl.intro(n, m, h, d, g, a, s, hs):
  match n m:
    case 0n _:
      star.intro(m, d, g, a, s, hs)
    case 1n+x 0n:
      false.elim(T(sem(d, g, atl(n, a), s, "")), h)
    case 1n+x 1n+y:
      seq2.with(d, g, a, exact(y, a), s, seq2.elim(d, g, a, exact(y, a), s, hs), T(sem(d, g, atl(n, a), s, "")), +s1 => +s2 => e => h1 => h2 => tr.x(d, g, Cat{a, Cat{atl(x, a), Emp{}}}, s1 ++ s2, s, e, seq2.intro(d, g, a, atl(x, a), s1, s2, h1, atl.intro(x, y, h, d, g, a, s2, h2))))

def AtlW(d: Nat, g: Gram, a: R, s: String, n: Nat) -> Type:
  &m: Nat -> T(Nat.is_le(n, m)) & T(sem(d, g, exact(m, a), s, ""))

law atl.k0:
  for -d: Nat
  for -g: Gram
  for -a: R
  for -s: String
  for w: ExW(d, g, a, s)
  AtlW(d, g, a, s, 0n)

def atl.k0(d, g, a, s, w):
  match w:
    case (+m, hm):
      (m, le0(m), hm)

law atl.k1:
  for -x: Nat
  for +d: Nat
  for +g: Gram
  for +a: R
  for -s: String
  for +s1: String
  for +s2: String
  for e: {s1 ++ s2 == s : String}
  for h1: T(sem(d, g, a, s1, ""))
  for w: AtlW(d, g, a, s2, x)
  AtlW(d, g, a, s, 1n+x)

def atl.k1(x, d, g, a, s, s1, s2, e, h1, w):
  match w:
    case (+m, hle, hm):
      (1n+m, hle, tr.x(d, g, Cat{a, Cat{exact(m, a), Emp{}}}, s1 ++ s2, s, e, seq2.intro(d, g, a, exact(m, a), s1, s2, h1, hm)))

law atl.elim:
  for +n: Nat
  for +d: Nat
  for +g: Gram
  for +a: R
  for +s: String
  for +hs: T(sem(d, g, atl(n, a), s, ""))
  AtlW(d, g, a, s, n)

def atl.elim(n, d, g, a, s, hs):
  match n:
    case 0n:
      atl.k0(d, g, a, s, star.elim(d, g, a, s, "", hs))
    case 1n+x:
      seq2.with(d, g, a, atl(x, a), s, seq2.elim(d, g, a, atl(x, a), s, hs), AtlW(d, g, a, s, 1n+x), +s1 => +s2 => e => h1 => h2 => atl.k1(x, d, g, a, s, s1, s2, e, h1, atl.elim(x, d, g, a, s2, h2)))

def rpt(a: Nat, b: Nat, +r: R) -> R:
  match a b:
    case 0n 0n:
      Emp{}
    case 0n 1n+y:
      Alt{Emp{}, Cat{r, Cat{rpt(0n, y, r), Emp{}}}}
    case 1n+x 0n:
      Bad{}
    case 1n+x 1n+y:
      Cat{r, Cat{rpt(x, y, r), Emp{}}}

law sem.alt.elim:
  for d: Nat
  for -g: Gram
  for -a: R
  for -b: R
  for -x: String
  for -p: String
  for h: T(sem(d, g, Alt{a, b}, x, p))
  T(orelse(sem(d, g, a, x, ""), u => sem(d, g, b, x, "")))

def sem.alt.elim(d, g, a, b, x, p, h):
  %Equal.sym(Bool, orelse(sem(d, g, a, x, ""), u => sem(d, g, b, x, "")), sem(d, g, Alt{a, b}, x, p), sem.alt(d, g, a, b, x, p)) : {_ == True{} : Bool}
  h

law sem.alt.left:
  for +d: Nat
  for +g: Gram
  for +a: R
  for -b: R
  for +x: String
  for -p: String
  for h: T(sem(d, g, a, x, ""))
  T(sem(d, g, Alt{a, b}, x, p))

def sem.alt.left(d, g, a, b, x, p, h):
  %sem.alt(d, g, a, b, x, p) : {_ == True{} : Bool}
  or.left(sem(d, g, a, x, ""), sem(d, g, b, x, ""), h)

law sem.alt.right:
  for +d: Nat
  for +g: Gram
  for +a: R
  for -b: R
  for +x: String
  for -p: String
  for h: T(sem(d, g, b, x, ""))
  T(sem(d, g, Alt{a, b}, x, p))

def sem.alt.right(d, g, a, b, x, p, h):
  %sem.alt(d, g, a, b, x, p) : {_ == True{} : Bool}
  or.right(sem(d, g, a, x, ""), sem(d, g, b, x, ""), h)

law sem.bad.elim:
  for d: Nat
  for -g: Gram
  for -x: String
  for -p: String
  for -C: Type
  for h: T(sem(d, g, Bad{}, x, p))
  C

def sem.bad.elim(d, g, x, p, C, h):
  match d:
    case 0n:
      false.elim(C, h)
    case 1n+e:
      false.elim(C, h)

law rpt.intro.no:
  for -x: Nat
  for m: Nat
  for ha: T(Nat.is_le(1n+x, m))
  for hb: T(Nat.is_le(m, 0n))
  T(False{})

def rpt.intro.no(x, m, ha, hb):
  match m:
    case 0n:
      ha
    case 1n+n:
      hb

law rpt.intro:
  for +a: Nat
  for +b: Nat
  for +m: Nat
  for ha: T(Nat.is_le(a, m))
  for hb: T(Nat.is_le(m, b))
  for +d: Nat
  for +g: Gram
  for +r: R
  for +s: String
  for hs: T(sem(d, g, exact(m, r), s, ""))
  T(sem(d, g, rpt(a, b, r), s, ""))

def rpt.intro(a, b, m, ha, hb, d, g, r, s, hs):
  match a b m:
    case 0n 0n 0n:
      hs
    case 0n 0n 1n+n:
      false.elim(T(sem(d, g, Emp{}, s, "")), hb)
    case 0n 1n+y 0n:
      sem.alt.left(d, g, Emp{}, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s, "", hs)
    case 0n 1n+y 1n+n:
      sem.alt.right(d, g, Emp{}, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s, "", seq2.with(d, g, r, exact(n, r), s, seq2.elim(d, g, r, exact(n, r), s, hs), T(sem(d, g, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s, "")), +s1 => +s2 => e => h1 => h2 => tr.x(d, g, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s1 ++ s2, s, e, seq2.intro(d, g, r, rpt(a, y, r), s1, s2, h1, rpt.intro(a, y, n, le0(n), hb, d, g, r, s2, h2)))))
    case 1n+x 0n _:
      false.elim(T(sem(d, g, Bad{}, s, "")), rpt.intro.no(x, m, ha, hb))
    case 1n+x 1n+y 0n:
      false.elim(T(sem(d, g, Cat{r, Cat{rpt(x, y, r), Emp{}}}, s, "")), ha)
    case 1n+x 1n+y 1n+n:
      seq2.with(d, g, r, exact(n, r), s, seq2.elim(d, g, r, exact(n, r), s, hs), T(sem(d, g, Cat{r, Cat{rpt(x, y, r), Emp{}}}, s, "")), +s1 => +s2 => e => h1 => h2 => tr.x(d, g, Cat{r, Cat{rpt(x, y, r), Emp{}}}, s1 ++ s2, s, e, seq2.intro(d, g, r, rpt(x, y, r), s1, s2, h1, rpt.intro(x, y, n, ha, hb, d, g, r, s2, h2))))

def RptW(d: Nat, g: Gram, r: R, s: String, a: Nat, b: Nat) -> Type:
  &m: Nat -> T(Nat.is_le(a, m)) & T(Nat.is_le(m, b)) & T(sem(d, g, exact(m, r), s, ""))

law rpt.k:
  for -a0: Nat
  for -a1: Nat
  for -b0: Nat
  for +d: Nat
  for +g: Gram
  for +r: R
  for -s: String
  for +s1: String
  for +s2: String
  for e: {s1 ++ s2 == s : String}
  for h1: T(sem(d, g, r, s1, ""))
  for f: @m: Nat -> T(Nat.is_le(a0, m)) -> T(Nat.is_le(a1, 1n+m))
  for w: RptW(d, g, r, s2, a0, b0)
  RptW(d, g, r, s, a1, 1n+b0)

def rpt.k(a0, a1, b0, d, g, r, s, s1, s2, e, h1, f, w):
  match w:
    case (+m, ha, hb, hm):
      (1n+m, f(m, ha), hb, tr.x(d, g, Cat{r, Cat{exact(m, r), Emp{}}}, s1 ++ s2, s, e, seq2.intro(d, g, r, exact(m, r), s1, s2, h1, hm)))

law rpt.elim:
  for +a: Nat
  for +b: Nat
  for +d: Nat
  for +g: Gram
  for +r: R
  for +s: String
  for +hs: T(sem(d, g, rpt(a, b, r), s, ""))
  RptW(d, g, r, s, a, b)

def rpt.elim(a, b, d, g, r, s, hs):
  match a b:
    case 0n 0n:
      (0n, {==}, {==}, hs)
    case 0n 1n+y:
      or.elim(sem(d, g, Emp{}, s, ""), sem(d, g, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s, ""), RptW(d, g, r, s, 0n, 1n+y), sem.alt.elim(d, g, Emp{}, Cat{r, Cat{rpt(a, y, r), Emp{}}}, s, "", hs), hz => (0n, {==}, {==}, hz), +hq => seq2.with(d, g, r, rpt(a, y, r), s, seq2.elim(d, g, r, rpt(a, y, r), s, hq), RptW(d, g, r, s, 0n, 1n+y), +s1 => +s2 => e => h1 => h2 => rpt.k(0n, 0n, y, d, g, r, s, s1, s2, e, h1, m => h => {==}, rpt.elim(a, y, d, g, r, s2, h2))))
    case 1n+x 0n:
      sem.bad.elim(d, g, s, "", RptW(d, g, r, s, 1n+x, 0n), hs)
    case 1n+x 1n+y:
      seq2.with(d, g, r, rpt(x, y, r), s, seq2.elim(d, g, r, rpt(x, y, r), s, hs), RptW(d, g, r, s, 1n+x, 1n+y), +s1 => +s2 => e => h1 => h2 => rpt.k(x, 1n+x, y, d, g, r, s, s1, s2, e, h1, m => h => h, rpt.elim(x, y, d, g, r, s2, h2)))

# ---- the fast matcher ----

type Op is Data:
  OLit{}
  OCls{}
  OAlt{}
  OCat{}
  OCatS{}
  OCatSC{}
  OStar{}
  OStarC{}
  ORefM{}
  ORef{}
  OEmp{}
  OBad{}
  ASelB{}
  ASelL{}
  ASelR{}
  ASelN{}

type St is Data:
  SNode{}
  SCat{}
  SCatL{}
  SCatA{}
  SAlt{}
  SAltR{}
  SAltM{}
  SStarH{}
  SStarA{}
  SStarK{}
  SRefM{}
  SStore{}

type UL is Data:
  UNil{}
  UCon{h: U32, t: UL}

type Entry is Data:
  ENone{}
  EOk{k: U32, h: U32, e: UL}

type V is Data:
  VNone{}
  VStuck{}
  VEnds{e: UL}
  VOne{x: U32}
  VNode{q: Op, w: U32}

type Out is Type:
  O{ops: Array<Op>, a: Array<U32>, m: Array<Entry>, v: V}

def low(w: U32) -> U32:
  (w .&. 65535 : U32)

def high(w: U32) -> U32:
  (w >> 16n : U32)

def call.k2(q: Op, ops: Array<Op>, m: Array<Entry>, p: Array<U32> & U32) -> Out:
  match p:
    case (a, x):
      O{ops, a, m, VNode{q, x}}

def call.k1(a: Array<U32>, m: Array<Entry>, +c: U32, p: Array<Op> & Op) -> Out:
  match p:
    case (ops, q):
      call.k2(q, ops, m, Array.get(U32, a, c))

def call(o: Out, +c: U32) -> Out:
  match o:
    case O{ops, a, m, v}:
      call.k1(a, m, c, Array.get(Op, ops, c))

def single(b: Bool, +i: U32) -> V:
  match b:
    case True{}:
      VOne{(i + 1 : U32)}
    case False{}:
      VEnds{UNil{}}

def vnorm(e: UL) -> V:
  match e:
    case UNil{}:
      VEnds{UNil{}}
    case UCon{+x, t}:
      match t:
        case UNil{}:
          VOne{x}
        case UCon{y, r}:
          VEnds{UCon{x, UCon{y, r}}}

def lit.k(+x: U32, +i: U32, ops: Array<Op>, m: Array<Entry>, p: Array<U32> & U32) -> Out:
  match p:
    case (a, c):
      O{ops, a, m, single(U32.is_eq(x, c), i)}

def lit.do(+x: U32, +i: U32, ops: Array<Op>, a: Array<U32>, m: Array<Entry>) -> Out:
  lit.k(x, i, ops, m, Array.get(U32, a, i))

def inr.b(p: Array<U32> & U32, k: Array<U32> -> U32 -> (Array<U32> & Bool)) -> Array<U32> & Bool:
  match p:
    case (a, x):
      k(a, x)

def inr.d(stop: Bool, hit: Bool, a: Array<U32>, k: Array<U32> -> (Array<U32> & Bool)) -> Array<U32> & Bool:
  match stop:
    case True{}:
      (a, False{})
    case False{}:
      match hit:
        case True{}:
          (a, True{})
        case False{}:
          k(a)

def inr(n: Nat, +j: U32, +c: U32, a: Array<U32>) -> Array<U32> & Bool:
  match n:
    case 0n:
      (a, False{})
    case 1n+m:
      inr.b(Array.get(U32, a, j), a1 => +lo => inr.b(Array.get(U32, a1, (j + 1 : U32)), a2 => +hi => inr.d(U32.is_gt(lo, hi), isle(lo, c, hi), a2, a3 => inr(m, (j + 2 : U32), c, a3))))

def cls.t2(p: Array<U32> & U32) -> Array<U32> & Bool:
  match p:
    case (a, x):
      (a, U32.is_eq(x, 1))

def cls.t(big: Bool, a: Array<U32>, +tb: U32, +c: U32) -> Array<U32> & Bool:
  match big:
    case False{}:
      cls.t2(Array.get(U32, a, (tb + c : U32)))
    case True{}:
      inr(64n, (tb + 128 : U32), c, a)

def cls.k2(+i: U32, ops: Array<Op>, m: Array<Entry>, p: Array<U32> & Bool) -> Out:
  match p:
    case (a, b):
      O{ops, a, m, single(b, i)}

def cls.k1(+tb: U32, +i: U32, ops: Array<Op>, m: Array<Entry>, p: Array<U32> & U32) -> Out:
  match p:
    case (a, +c):
      cls.k2(i, ops, m, cls.t(U32.is_ge(c, 128), a, tb, c))

def cls.do(+tb: U32, +i: U32, ops: Array<Op>, a: Array<U32>, m: Array<Entry>) -> Out:
  cls.k1(tb, i, ops, m, Array.get(U32, a, i))

def uapp(a: UL, b: UL) -> UL:
  match a:
    case UNil{}:
      b
    case UCon{h, t}:
      UCon{h, uapp(t, b)}

def merge.go(+f: Nat, o: Cmp, +x: U32, +y: U32, xt: UL, yt: UL) -> UL:
  match f:
    case 0n:
      UCon{x, UCon{y, uapp(xt, yt)}}
    case 1n+g:
      match o:
        case LT{}:
          match xt:
            case UNil{}:
              UCon{x, UCon{y, yt}}
            case UCon{+x2, xt2}:
              UCon{x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt)}
        case EQ{}:
          match xt:
            case UNil{}:
              UCon{x, yt}
            case UCon{+x2, xt2}:
              match yt:
                case UNil{}:
                  UCon{x, UCon{x2, xt2}}
                case UCon{+y2, yt2}:
                  UCon{x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2)}
        case GT{}:
          match yt:
            case UNil{}:
              UCon{y, UCon{x, xt}}
            case UCon{+y2, yt2}:
              UCon{y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2)}

def merge(a: UL, b: UL) -> UL:
  match a:
    case UNil{}:
      b
    case UCon{+x, xt}:
      match b:
        case UNil{}:
          UCon{x, xt}
        case UCon{+y, yt}:
          merge.go(4294967295n, U32.cmp(x, y), x, y, xt, yt)

def rev.go(l: UL, acc: UL) -> UL:
  match l:
    case UNil{}:
      acc
    case UCon{h, t}:
      rev.go(t, UCon{h, acc})

def rev(l: UL) -> UL:
  rev.go(l, UNil{})

def drop.k(same: Bool, h: U32, r: UL) -> UL:
  match same:
    case True{}:
      r
    case False{}:
      UCon{h, r}

def drop(+e: U32, l: UL) -> UL:
  match l:
    case UNil{}:
      UNil{}
    case UCon{+h, t}:
      drop.k(U32.is_eq(h, e), h, drop(e, t))

def setE(o: Out, e2: UL) -> Out:
  match o:
    case O{ops, a, m, v}:
      O{ops, a, m, vnorm(e2)}

def stuck(o: Out) -> Out:
  match o:
    case O{ops, a, m, v}:
      O{ops, a, m, VStuck{}}

def gbit(big: Bool, a: Array<U32>, +id: U32, +c: U32) -> Array<U32> & U32:
  match big:
    case True{}:
      (a, 1)
    case False{}:
      Array.get(U32, a, ((id + 1 : U32) + c : U32))

type F is Data:
  F{keep: Bool, cont: Bool}

def step.k3(+k: Bool, p: Array<U32> & Bool) -> Array<U32> & F:
  match p:
    case (a, b):
      (a, F{k, b})

def step.k2(+tb: U32, +c: U32, p: Array<U32> & U32) -> Array<U32> & F:
  match p:
    case (a, +k):
      step.k3(U32.is_eq(k, 1), cls.t(U32.is_ge(c, 128), a, tb, c))

def step.k1(+tb: U32, +gid: U32, p: Array<U32> & U32) -> Array<U32> & F:
  match p:
    case (a, +c):
      step.k2(tb, c, gbit(U32.is_ge(c, 128), a, gid, c))

def step(a: Array<U32>, +tb: U32, +gid: U32, +i: U32) -> Array<U32> & F:
  step.k1(tb, gid, Array.get(U32, a, i))

def scanf(+n: Nat, +tb: U32, +gid: U32, +i: U32, acc: UL, p: Array<U32> & F) -> Array<U32> & V:
  match n:
    case 0n:
      match p:
        case (a, f):
          (a, VStuck{})
    case 1n+m:
      match p:
        case (a, F{k, c}):
          match k:
            case True{}:
              match c:
                case True{}:
                  scanf(m, tb, gid, (i + 1 : U32), UCon{i, acc}, step(a, tb, gid, (i + 1 : U32)))
                case False{}:
                  (a, vnorm(rev(UCon{i, acc})))
            case False{}:
              match c:
                case True{}:
                  scanf(m, tb, gid, (i + 1 : U32), acc, step(a, tb, gid, (i + 1 : U32)))
                case False{}:
                  (a, vnorm(rev(acc)))

def scan.o(ops: Array<Op>, m: Array<Entry>, p: Array<U32> & V) -> Out:
  match p:
    case (a, v):
      O{ops, a, m, v}

def alt.k2(a: Array<U32>, m: Array<Entry>, p: Array<Op> & Op) -> Out:
  match p:
    case (ops, q):
      O{ops, a, m, VNode{q, 0}}

def alt.pick(big: Bool, ops: Array<Op>, a: Array<U32>, m: Array<Entry>, +id: U32, +c: U32) -> Out:
  match big:
    case True{}:
      O{ops, a, m, VNode{ASelB{}, 0}}
    case False{}:
      alt.k2(a, m, Array.get(Op, ops, ((id + 1 : U32) + c : U32)))

def alt.k1(ops: Array<Op>, m: Array<Entry>, +id: U32, p: Array<U32> & U32) -> Out:
  match p:
    case (a, +c):
      alt.pick(U32.is_ge(c, 128), ops, a, m, id, c)

def alt.sel(ops: Array<Op>, a: Array<U32>, m: Array<Entry>, +id: U32, +i: U32) -> Out:
  alt.k1(ops, m, id, Array.get(U32, a, i))

def kp.op(b: Bool) -> Op:
  match b:
    case True{}:
      ASelB{}
    case False{}:
      ASelN{}

def kp.k3(p: Array<U32> & U32, ops: Array<Op>, m: Array<Entry>) -> Out:
  match p:
    case (a, +b):
      O{ops, a, m, VNode{kp.op(U32.is_eq(b, 1)), 0}}

def kp.pick(big: Bool, ops: Array<Op>, a: Array<U32>, m: Array<Entry>, +id: U32, +c: U32) -> Out:
  match big:
    case True{}:
      O{ops, a, m, VNode{ASelB{}, 0}}
    case False{}:
      kp.k3(Array.get(U32, a, ((id + 1 : U32) + c : U32)), ops, m)

def kp.k1(ops: Array<Op>, m: Array<Entry>, +id: U32, p: Array<U32> & U32) -> Out:
  match p:
    case (a, +c):
      kp.pick(U32.is_ge(c, 128), ops, a, m, id, c)

def kp(ops: Array<Op>, a: Array<U32>, m: Array<Entry>, +id: U32, +i: U32) -> Out:
  kp.k1(ops, m, id, Array.get(U32, a, i))

def hash(+i: U32, +x: U32) -> U32:
  ((i * 37 : U32) + x : U32)

def probe.k2(hit: Bool, e: UL) -> V:
  match hit:
    case True{}:
      vnorm(e)
    case False{}:
      VNone{}

def probe.k1(ops: Array<Op>, a: Array<U32>, p: Array<Entry> & Entry, +i: U32, +w: U32) -> Out:
  match p:
    case (m, ent):
      match ent:
        case ENone{}:
          O{ops, a, m, VNone{}}
        case EOk{k, h, e}:
          O{ops, a, m, probe.k2(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), e)}

def probe(ops: Array<Op>, a: Array<U32>, m: Array<Entry>, +i: U32, +w: U32) -> Out:
  probe.k1(ops, a, Array.get(Entry, m, hash(i, w)), i, w)

def store(o: Out, +i: U32, +w: U32) -> Out:
  match o:
    case O{ops, a, m, v}:
      match v:
        case VEnds{+e}:
          O{ops, a, Array.set(Entry, m, hash(i, w), EOk{i, w, e}), VEnds{e}}
        case VOne{+x}:
          O{ops, a, Array.set(Entry, m, hash(i, w), EOk{i, w, UCon{x, UNil{}}}), VOne{x}}
        case _:
          O{ops, a, m, VStuck{}}

def go(+f: Nat, st: St, +id: U32, +i: U32, +w: U32, L: UL, acc: UL, o: Out) -> Out:
  match f:
    case 0n:
      stuck(o)
    case 1n+e:
      match st:
        case SNode{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VNode{q, +x}:
                  match q:
                    case OLit{}:
                      lit.do(x, i, ops, a, m)
                    case OCls{}:
                      cls.do(x, i, ops, a, m)
                    case OAlt{}:
                      go(e, SAlt{}, id, i, x, UNil{}, UNil{}, alt.sel(ops, a, m, id, i))
                    case OCat{}:
                      go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, low(x))))
                    case OCatS{}:
                      go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SStarH{}, id, i, low(x), UCon{i, UNil{}}, UNil{}, O{ops, a, m, VNone{}}))
                    case OCatSC{}:
                      go(e, SCat{}, id, i, x, UNil{}, UNil{}, scan.o(ops, m, scanf(e, low(x), id, i, UNil{}, step(a, low(x), id, i))))
                    case OStar{}:
                      go(e, SStarH{}, id, i, x, UCon{i, UNil{}}, UNil{}, O{ops, a, m, VNone{}})
                    case OStarC{}:
                      scan.o(ops, m, scanf(e, x, id, i, UNil{}, step(a, x, id, i)))
                    case ORefM{}:
                      go(e, SRefM{}, id, i, x, UNil{}, UNil{}, probe(ops, a, m, i, x))
                    case ORef{}:
                      go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, low(x)))
                    case OEmp{}:
                      O{ops, a, m, VOne{i}}
                    case OBad{}:
                      O{ops, a, m, VEnds{UNil{}}}
                    case _:
                      O{ops, a, m, VStuck{}}
                case _:
                  O{ops, a, m, VStuck{}}
        case SCat{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VOne{+y}:
                  go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, high(w)))
                case VEnds{r}:
                  match r:
                    case UNil{}:
                      O{ops, a, m, VEnds{UNil{}}}
                    case UCon{+y, t}:
                      match t:
                        case UNil{}:
                          go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, high(w)))
                        case UCon{y2, t2}:
                          go(e, SCatL{}, id, i, w, UCon{y, UCon{y2, t2}}, UNil{}, O{ops, a, m, VNone{}})
                case _:
                  O{ops, a, m, VStuck{}}
        case SCatL{}:
          match L:
            case UNil{}:
              setE(o, acc)
            case UCon{+y, t}:
              go(e, SCatA{}, id, i, w, t, acc, go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(o, high(w))))
        case SCatA{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VEnds{r}:
                  go(e, SCatL{}, id, i, w, L, merge(acc, r), O{ops, a, m, VNone{}})
                case VOne{+x}:
                  go(e, SCatL{}, id, i, w, L, merge(acc, UCon{x, UNil{}}), O{ops, a, m, VNone{}})
                case _:
                  O{ops, a, m, VStuck{}}
        case SAlt{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VNode{q, x2}:
                  match q:
                    case ASelB{}:
                      go(e, SAltR{}, id, i, w, UNil{}, UNil{}, go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, low(w))))
                    case ASelL{}:
                      go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, low(w)))
                    case ASelR{}:
                      go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, high(w)))
                    case ASelN{}:
                      O{ops, a, m, VEnds{UNil{}}}
                    case _:
                      O{ops, a, m, VStuck{}}
                case _:
                  O{ops, a, m, VStuck{}}
        case SAltR{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VEnds{x}:
                  go(e, SAltM{}, id, i, w, UNil{}, x, go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, high(w))))
                case VOne{+x}:
                  go(e, SAltM{}, id, i, w, UNil{}, UCon{x, UNil{}}, go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, high(w))))
                case _:
                  O{ops, a, m, VStuck{}}
        case SAltM{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VEnds{r}:
                  O{ops, a, m, vnorm(merge(acc, r))}
                case VOne{+x}:
                  O{ops, a, m, vnorm(merge(acc, UCon{x, UNil{}}))}
                case _:
                  O{ops, a, m, VStuck{}}
        case SStarH{}:
          match L:
            case UNil{}:
              setE(o, rev(acc))
            case UCon{+x, t}:
              go(e, SStarA{}, id, x, w, t, acc, go(e, SNode{}, w, x, 0, UNil{}, UNil{}, call(o, w)))
        case SStarA{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VEnds{r}:
                  go(e, SStarK{}, id, i, w, merge(L, drop(i, r)), acc, kp(ops, a, m, id, i))
                case VOne{+x}:
                  go(e, SStarK{}, id, i, w, merge(L, drop(i, UCon{x, UNil{}})), acc, kp(ops, a, m, id, i))
                case _:
                  O{ops, a, m, VStuck{}}
        case SStarK{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VNode{q, x2}:
                  match q:
                    case ASelB{}:
                      go(e, SStarH{}, id, i, w, L, UCon{i, acc}, O{ops, a, m, VNone{}})
                    case _:
                      go(e, SStarH{}, id, i, w, L, acc, O{ops, a, m, VNone{}})
                case _:
                  O{ops, a, m, VStuck{}}
        case SRefM{}:
          match o:
            case O{ops, a, m, v}:
              match v:
                case VEnds{r}:
                  O{ops, a, m, VEnds{r}}
                case VOne{+r}:
                  O{ops, a, m, VOne{r}}
                case VNone{}:
                  go(e, SStore{}, id, i, w, UNil{}, UNil{}, go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(O{ops, a, m, VNone{}}, low(w))))
                case _:
                  O{ops, a, m, VStuck{}}
        case SStore{}:
          store(o, i, w)

def refs(r: R, acc: +List<String>) -> +List<String>:
  match r:
    case Cat{a, b}:
      refs(a, refs(b, acc))
    case Alt{a, b}:
      refs(a, refs(b, acc))
    case Star{a}:
      refs(a, acc)
    case Ref{n}:
      Con{n, acc}
    case Emp{}:
      acc
    case Bad{}:
      acc
    case Lit{c}:
      acc
    case Rng{x, y}:
      acc

def seen(+n: String, vis: +List<String>) -> Bool:
  match vis:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, n), seen(n, t))

def reach.k2(b: Bool, k1: Unit -> Bool, k2: Unit -> Bool) -> Bool:
  match b:
    case True{}:
      k1(Unit{})
    case False{}:
      k2(Unit{})

def reach(+fl: Nat, +g: Gram, +target: String, +work: +List<String>, +vis: +List<String>) -> Bool:
  match fl:
    case 0n:
      True{}
    case 1n+p:
      match work:
        case Nil{}:
          False{}
        case Con{+x, t}:
          reach.k2(String.eq(String.to_lower(x), target), u => True{}, u => reach.k2(seen(String.to_lower(x), vis), v => reach(p, g, target, t, vis), v => reach(p, g, target, refs(lk(g, x), t), Con{String.to_lower(x), vis})))

def is_rec(+g: Gram, +n: String) -> Bool:
  reach(U32.to_nat(4096), g, String.to_lower(n), refs(lk(g, n), Nil{}), Nil{})

def simp.alt.k(y: R, x: R) -> R:
  match y:
    case Bad{}:
      x
    case Emp{}:
      Alt{x, Emp{}}
    case Lit{c}:
      Alt{x, Lit{c}}
    case Rng{a, b}:
      Alt{x, Rng{a, b}}
    case Cat{a, b}:
      Alt{x, Cat{a, b}}
    case Alt{a, b}:
      Alt{x, Alt{a, b}}
    case Star{a}:
      Alt{x, Star{a}}
    case Ref{n}:
      Alt{x, Ref{n}}

def simp.cat.k(y: R, x: R) -> R:
  match y:
    case Emp{}:
      x
    case Bad{}:
      Cat{x, Bad{}}
    case Lit{c}:
      Cat{x, Lit{c}}
    case Rng{a, b}:
      Cat{x, Rng{a, b}}
    case Cat{a, b}:
      Cat{x, Cat{a, b}}
    case Alt{a, b}:
      Cat{x, Alt{a, b}}
    case Star{a}:
      Cat{x, Star{a}}
    case Ref{n}:
      Cat{x, Ref{n}}

def inl.k(b: Bool, +n: String, k: Unit -> R) -> R:
  match b:
    case True{}:
      Ref{n}
    case False{}:
      k(Unit{})

def inl(+fl: Nat, +g: Gram, r: R) -> R:
  match fl:
    case 0n:
      r
    case 1n+p:
      match r:
        case Cat{a, b}:
          simp.cat.k(inl(fl, g, b), inl(fl, g, a))
        case Alt{a, b}:
          simp.alt.k(inl(fl, g, b), inl(fl, g, a))
        case Star{a}:
          Star{inl(fl, g, a)}
        case Ref{+n}:
          inl.k(is_rec(g, n), n, u => inl(p, g, lk(g, n)))
        case Emp{}:
          Emp{}
        case Bad{}:
          Bad{}
        case Lit{c}:
          Lit{c}
        case Rng{a, b}:
          Rng{a, b}

def inlg(+fl: Nat, +g: Gram, l: Gram) -> Gram:
  match l:
    case GNil{}:
      GNil{}
    case GCon{k, r, t}:
      GCon{k, inl(fl, g, r), inlg(fl, g, t)}

def refop(b: Bool) -> Op:
  match b:
    case True{}:
      ORefM{}
    case False{}:
      ORef{}

type B is Type:
  B{ops: Array<Op>, a: Array<U32>}

def bset(b: B, +id: U32, op: Op, +w: U32) -> B:
  match b:
    case B{ops, a}:
      B{Array.set(Op, ops, id, op), Array.set(U32, a, id, w)}

def bseta(b: B, +i: U32, +w: U32) -> B:
  match b:
    case B{ops, a}:
      B{ops, Array.set(U32, a, i, w)}

def bseto(b: B, +i: U32, op: Op) -> B:
  match b:
    case B{ops, a}:
      B{Array.set(Op, ops, i, op), a}

def leafy(r: R) -> Bool:
  match r:
    case Lit{c}:
      True{}
    case Rng{a, b}:
      True{}
    case Alt{a, b}:
      Bool.and(leafy(a), leafy(b))
    case Emp{}:
      False{}
    case Bad{}:
      False{}
    case Cat{a, b}:
      False{}
    case Star{a}:
      False{}
    case Ref{n}:
      False{}

def is_class(r: R) -> Bool:
  match r:
    case Rng{a, b}:
      True{}
    case Alt{a, b}:
      Bool.and(leafy(a), leafy(b))
    case Emp{}:
      False{}
    case Bad{}:
      False{}
    case Lit{c}:
      False{}
    case Cat{a, b}:
      False{}
    case Star{a}:
      False{}
    case Ref{n}:
      False{}

def lcount(r: R) -> U32:
  match r:
    case Alt{a, b}:
      (lcount(a) + lcount(b) : U32)
    case Lit{c}:
      1
    case Rng{a, b}:
      1
    case Emp{}:
      0
    case Bad{}:
      0
    case Cat{a, b}:
      0
    case Star{a}:
      0
    case Ref{n}:
      0

def csize(+r: R) -> U32:
  (((lcount(r) * 2 : U32) + 2 : U32) + 129 : U32)

def own(+cls: Bool, r: R) -> U32:
  match cls:
    case True{}:
      csize(r)
    case False{}:
      match r:
        case Alt{a, b}:
          129
        case Rng{a, b}:
          2
        case Emp{}:
          1
        case Bad{}:
          1
        case Lit{c}:
          1
        case Star{a}:
          129
        case Ref{n}:
          1
        case Cat{Star{z}, b}:
          129
        case Cat{a, b}:
          1

def rs.k(c: Bool, +r: R, k: Unit -> U32) -> U32:
  match c:
    case True{}:
      csize(r)
    case False{}:
      k(Unit{})

def rsize.go(r: R) -> U32:
  match r:
    case Emp{}:
      1
    case Bad{}:
      1
    case Lit{c}:
      1
    case Rng{a, b}:
      2
    case Star{+a}:
      (rs.k(is_class(a), a, u => rsize.go(a)) + 129 : U32)
    case Ref{n}:
      1
    case Cat{Star{+z}, +b}:
      ((rs.k(is_class(z), z, u => rsize.go(z)) + rs.k(is_class(b), b, u => rsize.go(b)) : U32) + 129 : U32)
    case Cat{+a, +b}:
      ((rs.k(is_class(a), a, u => rsize.go(a)) + rs.k(is_class(b), b, u => rsize.go(b)) : U32) + 1 : U32)
    case Alt{+a, +b}:
      ((rs.k(is_class(a), a, u => rsize.go(a)) + rs.k(is_class(b), b, u => rsize.go(b)) : U32) + 129 : U32)

def rsize(+r: R) -> U32:
  rs.k(is_class(r), r, u => rsize.go(r))

def root(+r: R, +next: U32) -> U32:
  (next + (rsize(r) - own(is_class(r), r) : U32) : U32)

type BL is Data:
  BNil{}
  BCon{h: Bool, t: BL}

type MV is Data:
  MV{n: Bool, s: BL}

def bl.or(+a: BL, +b: BL) -> BL:
  match a b:
    case BCon{x, xt} BCon{y, yt}:
      BCon{Bool.or(x, y), bl.or(xt, yt)}
    case _ _:
      BNil{}

def bl.const(n: Nat, +b: Bool) -> BL:
  match n:
    case 0n:
      BNil{}
    case 1n+p:
      BCon{b, bl.const(p, b)}

def bl.rng(n: Nat, +c: U32, +lo: U32, +hi: U32) -> BL:
  match n:
    case 0n:
      BNil{}
    case 1n+p:
      BCon{isle(lo, c, hi), bl.rng(p, (c + 1 : U32), lo, hi)}

def bl.and(+c: Bool, b: BL) -> BL:
  match c:
    case True{}:
      b
    case False{}:
      bl.const(128n, False{})

def mv.cat(ma: MV, mb: MV) -> MV:
  match ma mb:
    case MV{+na, sa} MV{nb, sb}:
      MV{Bool.and(na, nb), bl.or(sa, bl.and(na, sb))}

def mv.alt(ma: MV, mb: MV) -> MV:
  match ma mb:
    case MV{na, sa} MV{nb, sb}:
      MV{Bool.or(na, nb), bl.or(sa, sb)}

def mv.star(ma: MV) -> MV:
  match ma:
    case MV{na, sa}:
      MV{True{}, sa}

def mv(+fl: Nat, +g: Gram, r: R) -> MV:
  match fl:
    case 0n:
      MV{True{}, bl.const(128n, True{})}
    case 1n+p:
      match r:
        case Emp{}:
          MV{True{}, bl.const(128n, False{})}
        case Bad{}:
          MV{False{}, bl.const(128n, False{})}
        case Lit{+c}:
          MV{False{}, bl.rng(128n, 0, Char.to_u32(c), Char.to_u32(c))}
        case Rng{+x, +y}:
          MV{False{}, bl.rng(128n, 0, x, y)}
        case Cat{x, y}:
          mv.cat(mv(fl, g, x), mv(fl, g, y))
        case Alt{x, y}:
          mv.alt(mv(fl, g, x), mv(fl, g, y))
        case Star{x}:
          mv.star(mv(fl, g, x))
        case Ref{+n}:
          mv(p, g, lk(g, n))

def mv.may(m: MV) -> BL:
  match m:
    case MV{+n, s}:
      bl.or(bl.const(128n, n), s)

def sel(l: Bool, r: Bool) -> Op:
  match l r:
    case True{} True{}:
      ASelB{}
    case True{} False{}:
      ASelL{}
    case False{} True{}:
      ASelR{}
    case False{} False{}:
      ASelN{}

def wrsel(l: BL, r: BL, +i: U32, b: B) -> B:
  match l r:
    case BCon{x, xt} BCon{y, yt}:
      wrsel(xt, yt, (i + 1 : U32), bseto(b, i, sel(x, y)))
    case _ _:
      b

def cmatch(r: R, +c: U32) -> Bool:
  match r:
    case Lit{+x}:
      U32.is_eq(Char.to_u32(x), c)
    case Rng{+x, +y}:
      isle(x, c, y)
    case Alt{a, b}:
      Bool.or(cmatch(a, c), cmatch(b, c))
    case Emp{}:
      False{}
    case Bad{}:
      False{}
    case Cat{a, b}:
      False{}
    case Star{a}:
      False{}
    case Ref{n}:
      False{}

def wrcls.tb(n: Nat, +r: R, +c: U32, +i: U32, b: B) -> B:
  match n:
    case 0n:
      b
    case 1n+p:
      wrcls.tb(p, r, (c + 1 : U32), (i + 1 : U32), bseta(b, i, Bool.to_u32(cmatch(r, c))))

def wrcls.put(+x: U32, +y: U32, p: B & U32) -> B & U32:
  match p:
    case (b, +i):
      (bseta(bseta(b, i, x), (i + 1 : U32), y), (i + 2 : U32))

def wrcls.rg(r: R, p: B & U32) -> B & U32:
  match r:
    case Lit{+x}:
      wrcls.put(Char.to_u32(x), Char.to_u32(x), p)
    case Rng{+x, +y}:
      wrcls.put(x, y, p)
    case Alt{a, b}:
      wrcls.rg(b, wrcls.rg(a, p))
    case Emp{}:
      p
    case Bad{}:
      p
    case Cat{a, b}:
      p
    case Star{a}:
      p
    case Ref{n}:
      p

def wrcls.fin(p: B & U32) -> B:
  match p:
    case (b, +i):
      bseta(bseta(b, i, 1), (i + 1 : U32), 0)

def wrcls(+r: R, +next: U32, b: B) -> B:
  wrcls.fin(wrcls.rg(r, (bset(wrcls.tb(128n, r, 0, (next + 1 : U32), b), next, OCls{}, (next + 1 : U32)), (next + 129 : U32))))

type RT is Data:
  RNil{}
  RCon{n: String, root: U32, t: RT}

def simp0(r: R) -> R:
  match r:
    case Alt{a, Bad{}}:
      a
    case _:
      r

def body(+g: Gram, +k: String) -> R:
  simp0(lk(g, k))

def roots(+g: Gram, l: Gram, +next: U32) -> RT:
  match l:
    case GNil{}:
      RNil{}
    case GCon{+k, r, t}:
      +b = body(g, k)
      RCon{k, root(b, next), roots(g, t, (next + rsize(b) : U32))}

def tfind.k(e: Bool, +idx: U32, +x: U32, r: U32) -> U32:
  match e:
    case True{}:
      (x + (idx << 16n : U32) : U32)
    case False{}:
      r

def tfind.go(t: RT, +n: String, +idx: U32) -> U32:
  match t:
    case RNil{}:
      65535
    case RCon{k, x, r}:
      tfind.k(String.eq(String.to_lower(k), String.to_lower(n)), idx, x, tfind.go(r, n, (idx + 1 : U32)))

def tfind(+t: RT, +n: String) -> U32:
  tfind.go(t, n, 0)

def wr_ref2(+g: Gram, e: Bool, b: B, +id: U32, +rt: U32, +n: String) -> B:
  match e:
    case True{}:
      bset(b, id, OBad{}, 0)
    case False{}:
      bset(b, id, refop(is_rec(g, n)), rt)

def word2(+x: U32, +y: U32) -> U32:
  (x + (y << 16n : U32) : U32)

def wrbits(l: BL, +i: U32, b: B) -> B:
  match l:
    case BNil{}:
      b
    case BCon{x, t}:
      wrbits(t, (i + 1 : U32), bseta(b, i, Bool.to_u32(x)))

def emit.star.k(c: Bool, b: B, +a: R, +next: U32, +id: U32) -> B:
  match c:
    case True{}:
      wrbits(bl.const(128n, True{}), (id + 1 : U32), bset(b, id, OStarC{}, (next + 1 : U32)))
    case False{}:
      wrbits(bl.const(128n, True{}), (id + 1 : U32), bset(b, id, OStar{}, root(a, next)))

def emit.star(c: Bool, b: B, +a: R, +next: U32) -> B:
  +id = (next + rsize(a) : U32)
  emit.star.k(c, b, a, next, id)

def emit.alt(b: B, +g: Gram, +x: R, +y: R, +next: U32) -> B:
  +id = (next + (rsize(x) + rsize(y) : U32) : U32)
  wrsel(mv.may(mv(3n, g, x)), mv.may(mv(3n, g, y)), (id + 1 : U32), bset(b, id, OAlt{}, word2(root(x, next), root(y, (next + rsize(x) : U32)))))

def cats.op(c: Bool) -> Op:
  match c:
    case True{}:
      OCatSC{}
    case False{}:
      OCatS{}

def cats.lo(c: Bool, +z: R, +next: U32) -> U32:
  match c:
    case True{}:
      (next + 1 : U32)
    case False{}:
      root(z, next)

def emit.cats(b: B, +g: Gram, +z: R, +y: R, +next: U32, +c: Bool) -> B:
  +id = (next + (rsize(z) + rsize(y) : U32) : U32)
  wrbits(mv.may(mv(3n, g, y)), (id + 1 : U32), bset(b, id, cats.op(c), word2(cats.lo(c, z, next), root(y, (next + rsize(z) : U32)))))

def emit.k(c: Bool, +r: R, +next: U32, b: B, k: Unit -> B -> B) -> B:
  match c:
    case True{}:
      wrcls(r, next, b)
    case False{}:
      k(Unit{}, b)

def emit.go(+t: RT, +g: Gram, r: R, +next: U32, b: B) -> B:
  match r:
    case Emp{}:
      bset(b, next, OEmp{}, 0)
    case Bad{}:
      bset(b, next, OBad{}, 0)
    case Lit{+c}:
      bset(b, next, OLit{}, Char.to_u32(c))
    case Rng{+x, +y}:
      wrcls(Rng{x, y}, next, b)
    case Star{+a}:
      emit.star(is_class(a), emit.k(is_class(a), a, next, b, u => b2 => emit.go(t, g, a, next, b2)), a, next)
    case Ref{+n}:
      +rt = tfind(t, n)
      wr_ref2(g, U32.is_eq(rt, 65535), b, next, rt, n)
    case Cat{Star{+z}, +y}:
      emit.cats(emit.k(is_class(y), y, (next + rsize(z) : U32), emit.k(is_class(z), z, next, b, u => b2 => emit.go(t, g, z, next, b2)), u => b2 => emit.go(t, g, y, (next + rsize(z) : U32), b2)), g, z, y, next, is_class(z))
    case Cat{+x, +y}:
      bset(emit.k(is_class(y), y, (next + rsize(x) : U32), emit.k(is_class(x), x, next, b, u => b2 => emit.go(t, g, x, next, b2)), u => b2 => emit.go(t, g, y, (next + rsize(x) : U32), b2)), (next + (rsize(x) + rsize(y) : U32) : U32), OCat{}, word2(root(x, next), root(y, (next + rsize(x) : U32))))
    case Alt{+x, +y}:
      emit.alt(emit.k(is_class(y), y, (next + rsize(x) : U32), emit.k(is_class(x), x, next, b, u => b2 => emit.go(t, g, x, next, b2)), u => b2 => emit.go(t, g, y, (next + rsize(x) : U32), b2)), g, x, y, next)

def emit(+t: RT, +g: Gram, +r: R, +next: U32, b: B) -> B:
  emit.k(is_class(r), r, next, b, u => b2 => emit.go(t, g, r, next, b2))

def emit_all(+t: RT, +g: Gram, l: Gram, +next: U32, b: B) -> B & U32:
  match l:
    case GNil{}:
      (b, next)
    case GCon{+k, r, tl}:
      +bd = body(g, k)
      emit_all(t, g, tl, (next + rsize(bd) : U32), emit(t, g, bd, next, b))

def write(s: String, +i: U32, b: B) -> B & U32:
  match s:
    case SNil{}:
      (bseta(b, i, 4294967295), i)
    case SCon{+c, t}:
      write(t, (i + 1 : U32), bseta(b, i, Char.to_u32(c)))

def has(+z: U32, l: UL) -> Bool:
  match l:
    case UNil{}:
      False{}
    case UCon{h, t}:
      Bool.or(U32.is_eq(h, z), has(z, t))

def nul(+fl: Nat, +g: Gram, r: R) -> Bool:
  match fl:
    case 0n:
      True{}
    case 1n+p:
      match r:
        case Emp{}:
          True{}
        case Bad{}:
          False{}
        case Lit{x}:
          False{}
        case Rng{x, y}:
          False{}
        case Cat{x, y}:
          Bool.and(nul(fl, g, x), nul(fl, g, y))
        case Alt{x, y}:
          Bool.or(nul(fl, g, x), nul(fl, g, y))
        case Star{x}:
          True{}
        case Ref{+n}:
          nul(p, g, lk(g, n))

def fst(+fl: Nat, +g: Gram, r: R, +ch: U32) -> Bool:
  match fl:
    case 0n:
      True{}
    case 1n+p:
      match r:
        case Emp{}:
          False{}
        case Bad{}:
          False{}
        case Lit{+x}:
          U32.is_eq(Char.to_u32(x), ch)
        case Rng{+x, +y}:
          isle(x, ch, y)
        case Cat{+x, +y}:
          Bool.or(fst(fl, g, x, ch), Bool.and(nul(fl, g, x), fst(fl, g, y, ch)))
        case Alt{+x, +y}:
          Bool.or(fst(fl, g, x, ch), fst(fl, g, y, ch))
        case Star{x}:
          fst(fl, g, x, ch)
        case Ref{+n}:
          fst(p, g, lk(g, n), ch)

def may(+fl: Nat, +g: Gram, +r: R, +ch: U32) -> Bool:
  Bool.or(nul(fl, g, r), fst(fl, g, r, ch))

def and.k(p: B & Bool, k: B -> B & Bool) -> B & Bool:
  match p:
    case (b, v):
      match v:
        case False{}:
          (b, False{})
        case True{}:
          k(b)

def rd.o2(a: Array<U32>, k: B -> Op -> B & Bool, p: Array<Op> & Op) -> B & Bool:
  match p:
    case (ops, q):
      k(B{ops, a}, q)

def rdo(b: B, +i: U32, k: B -> Op -> B & Bool) -> B & Bool:
  match b:
    case B{ops, a}:
      rd.o2(a, k, Array.get(Op, ops, i))

def rd.u2(ops: Array<Op>, k: B -> U32 -> B & Bool, p: Array<U32> & U32) -> B & Bool:
  match p:
    case (a, x):
      k(B{ops, a}, x)

def rdu(b: B, +i: U32, k: B -> U32 -> B & Bool) -> B & Bool:
  match b:
    case B{ops, a}:
      rd.u2(ops, k, Array.get(U32, a, i))

def with(b: B, +i: U32, k: B -> Op -> U32 -> B & Bool) -> B & Bool:
  rdo(b, i, b1 => q => rdu(b1, i, b2 => x => k(b2, q, x)))

def badr(r: R) -> Bool:
  match r:
    case Bad{}:
      True{}
    case _:
      False{}

def is.olit(q: Op) -> Bool:
  match q:
    case OLit{}:
      True{}
    case _:
      False{}

def is.ocls(q: Op) -> Bool:
  match q:
    case OCls{}:
      True{}
    case _:
      False{}

def is.oemp(q: Op) -> Bool:
  match q:
    case OEmp{}:
      True{}
    case _:
      False{}

def is.obad(q: Op) -> Bool:
  match q:
    case OBad{}:
      True{}
    case _:
      False{}

type Kd is Data:
  KBit{}
  KL{}
  KR{}

def al.l(q: Op) -> Bool:
  match q:
    case ASelR{}:
      False{}
    case ASelN{}:
      False{}
    case _:
      True{}

def al.r(q: Op) -> Bool:
  match q:
    case ASelL{}:
      False{}
    case ASelN{}:
      False{}
    case _:
      True{}

def imp.b(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

def bi(a: Bool, b: Bool) -> Bool:
  match a b:
    case False{} False{}:
      True{}
    case False{} True{}:
      False{}
    case True{} False{}:
      False{}
    case True{} True{}:
      True{}

type P is Data:
  PCls{r: R, tb: U32}
  POne{id: U32}
  PRg{kd: Kd, id: U32, lo: U32, hi: U32}
  PAll{kd: Kd, id: U32}

def allow.l(kd: Kd, +id: U32, +k: U32, b: B) -> B & Bool:
  match kd:
    case KBit{}:
      rdu(b, ((id + 1 : U32) + k : U32), b1 => +x => (b1, U32.is_eq(x, 1)))
    case KL{}:
      rdo(b, ((id + 1 : U32) + k : U32), b1 => q => (b1, al.l(q)))
    case KR{}:
      rdo(b, ((id + 1 : U32) + k : U32), b1 => q => (b1, al.r(q)))

def imp.k(v: Bool, b: B, k: B -> B & Bool) -> B & Bool:
  match v:
    case False{}:
      (b, True{})
    case True{}:
      k(b)

def pr.l(p: P, +k: U32, b: B) -> B & Bool:
  match p:
    case PCls{+r, +tb}:
      rdu(b, (tb + k : U32), b1 => +x => (b1, bi(U32.is_eq(x, 1), cmatch(r, k))))
    case POne{+id}:
      rdu(b, ((id + 1 : U32) + k : U32), b1 => +x => (b1, U32.is_eq(x, 1)))
    case PRg{+kd, +id, +x, +y}:
      imp.k(isle(x, k, y), b, b1 => allow.l(kd, id, k, b1))
    case PAll{+kd, +id}:
      allow.l(kd, id, k, b)

def all.l(+p: P, n: Nat, +k: U32, b: B) -> B & Bool:
  match n:
    case 0n:
      (b, True{})
    case 1n+m:
      and.k(pr.l(p, k, b), b1 => all.l(p, m, (k + 1 : U32), b1))

type LP is Data:
  LNil{}
  LCon{lo: U32, hi: U32, t: LP}

def lv(r: R, acc: LP) -> LP:
  match r:
    case Lit{+x}:
      LCon{Char.to_u32(x), Char.to_u32(x), acc}
    case Rng{+x, +y}:
      LCon{x, y, acc}
    case Alt{a, b}:
      lv(a, lv(b, acc))
    case _:
      acc

def rng.l(l: LP, n: Nat, +j: U32, b: B) -> B & Bool:
  match l:
    case LNil{}:
      rdu(b, j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => (b2, U32.is_gt(lo, hi))))
    case LCon{+x, +y, t}:
      match n:
        case 0n:
          (b, False{})
        case 1n+m:
          rdu(b, j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => and.k((b2, Bool.and(Bool.and(U32.is_eq(lo, x), U32.is_eq(hi, y)), Bool.not(U32.is_gt(x, y)))), b3 => rng.l(t, m, (j + 2 : U32), b3))))

def cls.l(+r: R, +tb: U32, b: B) -> B & Bool:
  and.k((b, Bool.and(leafy(r), Bool.not(cmatch(r, 4294967295)))), b1 => and.k(all.l(PCls{r, tb}, 128n, 0, b1), b2 => rng.l(lv(r, LNil{}), 64n, (tb + 128 : U32), b2)))

def ck.fst(+kd: Kd, +fl: Nat, +g: Gram, r: R, +id: U32, b: B) -> B & Bool:
  match fl:
    case 0n:
      all.l(PAll{kd, id}, 128n, 0, b)
    case 1n+p:
      match r:
        case Emp{}:
          (b, True{})
        case Bad{}:
          (b, True{})
        case Lit{+x}:
          imp.k(Bool.not(U32.is_ge(Char.to_u32(x), 128)), b, b1 => allow.l(kd, id, Char.to_u32(x), b1))
        case Rng{+x, +y}:
          all.l(PRg{kd, id, x, y}, 128n, 0, b)
        case Cat{+a1, +b1}:
          and.k(ck.fst(kd, fl, g, a1, id, b), b2 => imp.k(nul(fl, g, a1), b2, b3 => ck.fst(kd, fl, g, b1, id, b3)))
        case Alt{+a1, +b1}:
          and.k(ck.fst(kd, fl, g, a1, id, b), b2 => ck.fst(kd, fl, g, b1, id, b2))
        case Star{+x}:
          ck.fst(kd, fl, g, x, id, b)
        case Ref{+n}:
          ck.fst(kd, p, g, lk(g, n), id, b)

def ck.may(+kd: Kd, +g: Gram, +y: R, +id: U32, b: B) -> B & Bool:
  and.k(imp.k(nul(3n, g, y), b, b1 => all.l(PAll{kd, id}, 128n, 0, b1)), b2 => ck.fst(kd, 3n, g, y, id, b2))

def ref.go(t: RT, +n: String, +h: U32, +root: U32) -> Bool:
  match t:
    case RNil{}:
      False{}
    case RCon{+k, +x, r}:
      Bool.or(Bool.and(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root))), Bool.and(Bool.not(U32.is_eq(h, 0)), ref.go(r, n, (h - 1 : U32), root)))

def chk.at(+g: Gram, +t: RT, r: R, q: Op, +x: U32, +id: U32, b: B) -> B & Bool:
  match r:
    case Emp{}:
      (b, is.oemp(q))
    case Bad{}:
      (b, is.obad(q))
    case Lit{+h}:
      (b, Bool.and(is.olit(q), Bool.and(U32.is_eq(x, Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)))))
    case Rng{+lo, +hi}:
      and.k((b, is.ocls(q)), b1 => cls.l(Rng{lo, hi}, x, b1))
    case Cat{a1, +y}:
      match a1:
        case Star{+z}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Star{z}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case OCatS{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, z, q9, x9, low(x), b9)), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, g, y, id, b2)))
            case OCatSC{}:
              and.k(cls.l(z, low(x), b), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, g, y, id, b2)))
            case _:
              (b, False{})
        case Emp{}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Emp{}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Bad{}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Bad{}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Lit{+c0}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Lit{c0}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Rng{+p0, +p1}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Rng{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Cat{+p0, +p1}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Cat{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Alt{+p0, +p1}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Alt{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
        case Ref{+p0}:
          match q:
            case OCat{}:
              and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, Ref{p0}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, y, q9, x9, high(x), b9)))
            case _:
              (b, False{})
    case Alt{+a1, +b2}:
      match q:
        case OCls{}:
          cls.l(Alt{a1, b2}, x, b)
        case OAlt{}:
          and.k(with(b, low(x), b9 => q9 => +x9 => chk.at(g, t, a1, q9, x9, low(x), b9)), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(g, t, b2, q9, x9, high(x), b9)), b3 => and.k(ck.may(KL{}, g, a1, id, b3), b5 => ck.may(KR{}, g, b2, id, b5))))
        case _:
          (b, False{})
    case Star{+a1}:
      match q:
        case OStar{}:
          and.k(with(b, x, b9 => q9 => +x9 => chk.at(g, t, a1, q9, x9, x, b9)), b1 => all.l(POne{id}, 128n, 0, b1))
        case OStarC{}:
          and.k(cls.l(a1, x, b), b1 => all.l(POne{id}, 128n, 0, b1))
        case _:
          (b, False{})
    case Ref{+n}:
      match q:
        case ORefM{}:
          (b, ref.go(t, n, high(x), low(x)))
        case ORef{}:
          (b, ref.go(t, n, high(x), low(x)))
        case OBad{}:
          (b, badr(lk(g, n)))
        case _:
          (b, False{})

def rules.l(+g: Gram, +t: RT, l: RT, b: B) -> B & Bool:
  match l:
    case RNil{}:
      (b, True{})
    case RCon{+k, +x, r}:
      and.k(with(b, x, b9 => q9 => +x9 => chk.at(g, t, body(g, k), q9, x9, x, b9)), b1 => rules.l(g, t, r, b1))

def text.a(s: String, +i: U32, +end: U32, ok: Bool, p: Array<U32> & U32) -> Array<U32> & Bool:
  match s:
    case SNil{}:
      match p:
        case (a, +x):
          (a, Bool.and(ok, Bool.and(U32.is_eq(x, 4294967295), U32.is_eq(i, end))))
    case SCon{+h, t}:
      match p:
        case (a, +x):
          text.a(t, (i + 1 : U32), end, Bool.and(ok, Bool.and(U32.is_eq(x, Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)))), Array.get(U32, a, (i + 1 : U32)))

def text.fin(ops: Array<Op>, p: Array<U32> & Bool) -> B & Bool:
  match p:
    case (a, v):
      (B{ops, a}, v)

def text.l(s: String, +i: U32, +end: U32, b: B) -> B & Bool:
  match b:
    case B{ops, a}:
      text.fin(ops, text.a(s, i, end, True{}, Array.get(U32, a, i)))

def validate(+g: Gram, +t: RT, +r: R, +root: U32, +s: String, +st0: U32, +end: U32, b: B) -> B & Bool:
  and.k(rules.l(g, t, t, b), b1 => and.k(with(b1, root, b9 => q9 => +x9 => chk.at(g, t, r, q9, x9, root, b9)), b2 => text.l(s, st0, end, b2)))

def fast.fin(o: Out, +z: U32) -> Maybe<&2, Bool>:
  match o:
    case O{ops, a, m, v}:
      match v:
        case VEnds{e}:
          Some{has(z, e)}
        case VOne{+x}:
          Some{U32.is_eq(x, z)}
        case _:
          None{}

def bits.k(b: Bool, k: Unit -> Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+k(Unit{})

def bits(d: Nat, +x: U32) -> Nat:
  match d:
    case 0n:
      0n
    case 1n+p:
      bits.k(U32.is_eq(x, 0), u => bits(p, U32.shr(x)))

def fast.run(b: B, +rt: U32, +f: Nat, +end: U32, +st0: U32) -> Maybe<&2, Bool>:
  match b:
    case B{ops, a}:
      fast.fin(go(f, SNode{}, rt, st0, 0, UNil{}, UNil{}, call(O{ops, a, [ENone{} : Entry^Nat.min(20n, 1n+bits(32n, end))], VNone{}}, rt)), end)

def fast.fin3(p: B & Bool, +rt: U32, +f: Nat, +end: U32, +st0: U32) -> Maybe<&2, Bool>:
  match p:
    case (b, ok):
      match ok:
        case True{}:
          fast.run(b, rt, f, end, st0)
        case False{}:
          None{}

def fast.fin2(p: B & U32, +g: Gram, +t: RT, +r: R, +s: String, +rt: U32, +f: Nat, +st0: U32) -> Maybe<&2, Bool>:
  match p:
    case (b, +e):
      fast.fin3(validate(g, t, r, rt, s, st0, e, b), rt, f, e, st0)

def fast.text(b: B, +g: Gram, +t: RT, +r: R, +nx: U32, +rt: U32, +s: String) -> Maybe<&2, Bool>:
  fast.fin2(write(s, nx, b), g, t, r, s, rt, Nat.add(Nat.mul(64n, String.length(s)), 4096n), nx)

def fast.k(p: B & U32, +t: RT, +g: Gram, +r: R, +s: String) -> Maybe<&2, Bool>:
  match p:
    case (b, +nx):
      fast.text(emit(t, g, r, nx, b), g, t, r, (nx + rsize(r) : U32), root(r, nx), s)

def gsize(g: Gram, +base: Gram) -> U32:
  match g:
    case GNil{}:
      0
    case GCon{+k, r, t}:
      (rsize(body(base, k)) + gsize(t, base) : U32)

def fast.go(+g: Gram, +r: R, +s: String, +code: U32, +n: U32) -> Maybe<&2, Bool>:
  +t = roots(g, g, 16)
  fast.k(emit_all(t, g, g, 16, B{[OEmp{} : Op^bits(32n, code)], [0 : U32^bits(32n, (code + n : U32))]}), t, g, r, s)

def fast.size(ok: Bool, +g: Gram, +r: R, +s: String, +code: U32) -> Maybe<&2, Bool>:
  match ok:
    case True{}:
      fast.go(g, r, s, code, (U32.from_nat(String.length(s)) + 4 : U32))
    case False{}:
      None{}

def fast(+g0: Gram, r: R, +s: String) -> Maybe<&2, Bool>:
  +g = inlg(12n, g0, g0)
  +r2 = inl(12n, g0, r)
  +code = ((gsize(g, g) + rsize(r2) : U32) + 32 : U32)
  fast.size(U32.is_lt(code, 60000), g, r2, s, code)

def full.pick(m: Maybe<&2, Bool>, k: Unit -> Bool) -> Bool:
  match m:
    case None{}:
      k(Unit{})
    case Some{b}:
      b

def full.go(+g: Gram, +r: R, +s: String) -> Bool:
  full.pick(fast(g, r, s), u => sem(1n+bound(g, s), g, r, s, ""))

# Matching on s first keeps the checker from running the compiler on an open string.
def full.run(+g: Gram, +r: R, s: String) -> Bool:
  match s:
    case SNil{}:
      full.go(g, r, SNil{})
    case SCon{+h, +t}:
      full.go(g, r, SCon{h, t})

# ---- arrays: reading keeps the array, and memo leaves stay valid ----

type Tree<-T: Data> is Data:
  TLeaf{v: T}
  TNode{l: Tree<T>, r: Tree<T>}

def unshadow(-T: Data, t: Tree<T>) -> Array<T>:
  match t:
    case TLeaf{x}:
      ALeaf{x}
    case TNode{xs, ys}:
      ANode{unshadow(T, xs), unshadow(T, ys)}

law shape.eq:
  for -T: Data
  for -t1: Tree<T>
  for -t2: Tree<T>
  for -xs: Array<T>
  for -ys: Array<T>
  for e1: {unshadow(T, t1) == xs : Array<T>}
  for e2: {unshadow(T, t2) == ys : Array<T>}
  {ANode{unshadow(T, t1), unshadow(T, t2)} == ANode{xs, ys} : Array<T>}

def shape.eq(T, t1, t2, xs, ys, e1, e2):
  %e1 : {ANode{unshadow(T, t1), unshadow(T, t2)} == ANode{_, ys} : Array<T>}
  %e2 : {ANode{unshadow(T, t1), unshadow(T, t2)} == ANode{unshadow(T, t1), _} : Array<T>}
  {==}

law shape.k:
  for -T: Data
  for -xs: Array<T>
  for -ys: Array<T>
  for w1: &t: Tree<T> -> {unshadow(T, t) == xs : Array<T>}
  for w2: &t: Tree<T> -> {unshadow(T, t) == ys : Array<T>}
  exs t: Tree<T>
  {unshadow(T, t) == ANode{xs, ys} : Array<T>}

def shape.k(T, xs, ys, w1, w2):
  match w1:
    case (+t1, e1):
      match w2:
        case (+t2, e2):
          (TNode{t1, t2}, shape.eq(T, t1, t2, xs, ys, e1, e2))

law shape:
  for -T: Data
  for a: Array<T>
  exs t: Tree<T>
  {unshadow(T, t) == a : Array<T>}

def shape(T, a):
  match a:
    case ALeaf{+x}:
      (TLeaf{x}, {==})
    case ANode{xs0, ys0}:
      shape.k(T, xs0, ys0, shape(T, xs0), shape(T, ys0))

def snd1(-T: Data, p: Array<T> & T) -> T:
  match p:
    case (a, x):
      x

def snd.u(-T: Type, p: Array<T> & U32) -> U32:
  match p:
    case (a, n):
      n

law size.same:
  for -T: Data
  for +t: Tree<T>
  {(unshadow(T, t), snd.u(T, Array.size(T, unshadow(T, t)))) == Array.size(T, unshadow(T, t)) : Array<T> & U32}

def size.same(T, t):
  match t:
    case TLeaf{x}:
      {==}
    case TNode{xs, ys}:
      %size.same(T, xs) : {(ANode{unshadow(T, xs), unshadow(T, ys)}, snd.u(T, Array.size.node(T, unshadow(T, ys), _))) == Array.size.node(T, unshadow(T, ys), _) : Array<T> & U32}
      {==}

law get.go.same:
  for -T: Data
  for +t: Tree<T>
  for +n: U32
  for +i: U32
  for z: Bool
  {(unshadow(T, t), snd1(T, Array.get.go(T, unshadow(T, t), n, i, z))) == Array.get.go(T, unshadow(T, t), n, i, z) : Array<T> & T}

def get.go.same(T, t, n, i, z):
  match t z:
    case TLeaf{+x} _:
      {==}
    case TNode{xs, ys} True{}:
      %get.go.same(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) : {(ANode{unshadow(T, xs), unshadow(T, ys)}, snd1(T, Array.swap.lo(T, unshadow(T, ys), _))) == Array.swap.lo(T, unshadow(T, ys), _) : Array<T> & T}
      {==}
    case TNode{xs, ys} False{}:
      %get.go.same(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) : {(ANode{unshadow(T, xs), unshadow(T, ys)}, snd1(T, Array.swap.hi(T, unshadow(T, xs), _))) == Array.swap.hi(T, unshadow(T, xs), _) : Array<T> & T}
      {==}

def tr.rd(-T: Data, t: Tree<T>, +i: U32) -> T:
  snd1(T, Array.get(T, unshadow(T, t), i))

law get.same:
  for -T: Data
  for +t: Tree<T>
  for +i: U32
  {(unshadow(T, t), tr.rd(T, t, i)) == Array.get(T, unshadow(T, t), i) : Array<T> & T}

law get.same.k:
  for -T: Data
  for +n: U32
  for +i: U32
  for +t: Tree<T>
  {(unshadow(T, t), snd1(T, Array.get.at(T, i, (unshadow(T, t), n)))) == Array.get.at(T, i, (unshadow(T, t), n)) : Array<T> & T}

def get.same.k(T, n, i, t):
  get.go.same(T, t, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))

def get.same(T, t, i):
  %size.same(T, t) : {(unshadow(T, t), snd1(T, Array.get.at(T, i, _))) == Array.get.at(T, i, _) : Array<T> & T}
  get.same.k(T, snd.u(T, Array.size(T, unshadow(T, t))), i, t)

# ---- equality on words and strings ----

def cmp.d.eq(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

law lt.not.eq:
  for h: {LT{} == EQ{} : Cmp}
  Empty

def lt.not.eq(h):
  %h : cmp.d.eq(_)
  Unit{}

law gt.not.eq:
  for h: {GT{} == EQ{} : Cmp}
  Empty

def gt.not.eq(h):
  %h : cmp.d.eq(_)
  Unit{}

law bool.cmp.eq:
  for a: Bool
  for b: Bool
  for h: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

def bool.cmp.eq(a, b, h):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      absurd({False{} == True{} : Bool}, lt.not.eq(h))
    case True{} False{}:
      absurd({True{} == False{} : Bool}, gt.not.eq(h))
    case True{} True{}:
      {==}

law fin.eq.tail:
  for a: Bool
  for b: Bool
  for t: Cmp
  for h: {Word.cmp.fin(a, b, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

def fin.eq.tail(a, b, t, h):
  match t:
    case LT{}:
      absurd({LT{} == EQ{} : Cmp}, lt.not.eq(h))
    case EQ{}:
      {==}
    case GT{}:
      absurd({GT{} == EQ{} : Cmp}, gt.not.eq(h))

law fin.eq.head:
  for a: Bool
  for b: Bool
  for t: Cmp
  for h: {Word.cmp.fin(a, b, t) == EQ{} : Cmp}
  {a == b : Bool}

def fin.eq.head(a, b, t, h):
  match t:
    case LT{}:
      absurd({a == b : Bool}, lt.not.eq(h))
    case EQ{}:
      bool.cmp.eq(a, b, h)
    case GT{}:
      absurd({a == b : Bool}, gt.not.eq(h))

law word.eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +h: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

law word.con.eq:
  for -p: Nat
  for -ab: Bool
  for -bb: Bool
  for -at: Word(p)
  for -bt: Word(p)
  for h1: {ab == bb : Bool}
  for h2: {at == bt : Word(p)}
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}

def word.con.eq(p, ab, bb, at, bt, h1, h2):
  %h1 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  %h2 : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
  {==}

def word.eq(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          word.con.eq(p, ab, bb, at, bt, fin.eq.head(ab, bb, Word.cmp(p, at, bt), h), word.eq(p, at, bt, fin.eq.tail(ab, bb, Word.cmp(p, at, bt), h)))

law iseq.eq:
  for c: Cmp
  for h: T(Cmp.is_eq(c))
  {c == EQ{} : Cmp}

def iseq.eq(c, h):
  match c:
    case LT{}:
      false.elim({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      false.elim({GT{} == EQ{} : Cmp}, h)

law u32.eq.t:
  for a: U32
  for b: U32
  for h: T(U32.is_eq(a, b))
  {a == b : U32}

def u32.eq.t(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, v => U32{v}, x, y, word.eq(32n, x, y, iseq.eq(Word.cmp(32n, x, y), h)))

law word.refl:
  for +n: Nat
  for a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def word.refl.k(a: Bool, -t: Cmp, h: {t == EQ{} : Cmp}) -> {Word.cmp.fin(a, a, t) == EQ{} : Cmp}:
  match a:
    case False{}:
      %Equal.sym(Cmp, t, EQ{}, h) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
      {==}
    case True{}:
      %Equal.sym(Cmp, t, EQ{}, h) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
      {==}

def word.refl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{+b, +t}:
          word.refl.k(b, Word.cmp(p, t, t), word.refl(p, t))

law u32.refl:
  for a: U32
  T(U32.is_eq(a, a))

def u32.refl(a):
  match a:
    case U32{+x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word.refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# ---- strings ----

law order.c:
  for c: Cmp
  for a: String
  for b: String
  for h: T(Cmp.is_eq(String.order.go(a, b, c)))
  {c == EQ{} : Cmp}

def order.c(c, a, b, h):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      match a b:
        case SNil{} SNil{}:
          false.elim({LT{} == EQ{} : Cmp}, h)
        case SNil{} SCon{Chr{x}, t}:
          false.elim({LT{} == EQ{} : Cmp}, h)
        case SCon{Chr{x}, t} SNil{}:
          false.elim({LT{} == EQ{} : Cmp}, h)
        case SCon{Chr{x}, t} SCon{Chr{y}, u}:
          false.elim({LT{} == EQ{} : Cmp}, h)
    case GT{}:
      match a b:
        case SNil{} SNil{}:
          false.elim({GT{} == EQ{} : Cmp}, h)
        case SNil{} SCon{Chr{x}, t}:
          false.elim({GT{} == EQ{} : Cmp}, h)
        case SCon{Chr{x}, t} SNil{}:
          false.elim({GT{} == EQ{} : Cmp}, h)
        case SCon{Chr{x}, t} SCon{Chr{y}, u}:
          false.elim({GT{} == EQ{} : Cmp}, h)

law char.eq:
  for -a: U32
  for -b: U32
  for -t: String
  for -u: String
  for e1: {a == b : U32}
  for e2: {t == u : String}
  {SCon{Chr{a}, t} == SCon{Chr{b}, u} : String}

def char.eq(a, b, t, u, e1, e2):
  %e1 : {SCon{Chr{a}, t} == SCon{Chr{_}, u} : String}
  %e2 : {SCon{Chr{a}, t} == SCon{Chr{a}, _} : String}
  {==}

law order.rw:
  for -t: String
  for -u: String
  for -c: Cmp
  for e: {c == EQ{} : Cmp}
  for h: T(Cmp.is_eq(String.order.go(t, u, c)))
  T(Cmp.is_eq(String.order.go(t, u, EQ{})))

def order.rw(t, u, c, e, h):
  %e : {Cmp.is_eq(String.order.go(t, u, _)) == True{} : Bool}
  h

law str.eq.c:
  for +x: U32
  for +y: U32
  for +t: String
  for +u: String
  for h: T(Cmp.is_eq(String.order.go(t, u, U32.cmp(x, y))))
  {x == y : U32}

def str.eq.c(x, y, t, u, h):
  match x y:
    case U32{+p} U32{+q}:
      Equal.cong(Word(32n), U32, v => U32{v}, p, q, word.eq(32n, p, q, order.c(Word.cmp(32n, p, q), t, u, h)))

law str.eq.t:
  for a: String
  for b: String
  for +h: T(String.eq(a, b))
  {a == b : String}

def str.eq.t(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{+x}, +t}:
      false.elim({SNil{} == SCon{Chr{x}, t} : String}, h)
    case SCon{Chr{+x}, +t} SNil{}:
      false.elim({SCon{Chr{x}, t} == SNil{} : String}, h)
    case SCon{Chr{+x}, +t} SCon{Chr{+y}, +u}:
      char.eq(x, y, t, u, str.eq.c(x, y, t, u, h), str.eq.t(t, u, order.rw(t, u, U32.cmp(x, y), order.c(U32.cmp(x, y), t, u, h), h)))

law order.refl.k:
  for +x: U32
  {U32.cmp(x, x) == EQ{} : Cmp}

def order.refl.k(x):
  match x:
    case U32{+w}:
      word.refl(32n, w)

law str.refl:
  for a: String
  T(String.eq(a, a))

def str.refl(a):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, order.refl.k(x)) : {Cmp.is_eq(String.order.go(t, t, _)) == True{} : Bool}
      str.refl(t)

# ---- the ghost context ----

type Cx is Data:
  Cx{g: Gram, S: String, nx: U32, rt: RT, tO: Tree<Op>, tA: Tree<U32>}

def cg(c: Cx) -> Gram:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      g

def cg2(+c: Cx) -> Gram:
  inlg(12n, cg(c), cg(c))

def cS(c: Cx) -> String:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      S

def cnx(c: Cx) -> U32:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      nx

def crt(c: Cx) -> RT:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      rt

def cO(c: Cx) -> Tree<Op>:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      tO

def cA(c: Cx) -> Tree<U32>:
  match c:
    case Cx{g, S, nx, rt, tO, tA}:
      tA

def rdA(+c: Cx, +i: U32) -> U32:
  tr.rd(U32, cA(c), i)

def rdO(+c: Cx, +i: U32) -> Op:
  tr.rd(Op, cO(c), i)

def B0(+c: Cx) -> Nat:
  bound(cg(c), cS(c))

def TR(+c: Cx, r: R, +y: String) -> Bool:
  sem(1n+B0(c), cg(c), r, y, "")

# ---- Bool facts ----

law and.i:
  for a: Bool
  for -b: Bool
  for ha: T(a)
  for hb: T(b)
  T(Bool.and(a, b))

def and.i(a, b, ha, hb):
  match a:
    case False{}:
      false.elim(T(False{}), ha)
    case True{}:
      hb

law and.l:
  for a: Bool
  for -b: Bool
  for h: T(Bool.and(a, b))
  T(a)

def and.l(a, b, h):
  match a:
    case False{}:
      h
    case True{}:
      {==}

law and.r:
  for a: Bool
  for -b: Bool
  for h: T(Bool.and(a, b))
  T(b)

def and.r(a, b, h):
  match a:
    case False{}:
      false.elim(T(b), h)
    case True{}:
      h

law or.l:
  for a: Bool
  for -b: Bool
  for h: T(a)
  T(Bool.or(a, b))

def or.l(a, b, h):
  match a:
    case False{}:
      false.elim(T(b), h)
    case True{}:
      {==}

law or.r:
  for a: Bool
  for -b: Bool
  for h: T(b)
  T(Bool.or(a, b))

def or.r(a, b, h):
  match a:
    case False{}:
      h
    case True{}:
      {==}

def or.c(a: Bool, -b: Bool, -C: Type, h: T(Bool.or(a, b)), f: T(a) -> C, k: T(b) -> C) -> C:
  match a:
    case False{}:
      k(h)
    case True{}:
      f({==})

law bi.lr:
  for a: Bool
  for b: Bool
  for h: T(bi(a, b))
  for ha: T(a)
  T(b)

def bi.lr(a, b, h, ha):
  match a b:
    case False{} False{}:
      false.elim(T(False{}), ha)
    case False{} True{}:
      {==}
    case True{} False{}:
      false.elim(T(False{}), h)
    case True{} True{}:
      {==}

law bi.rl:
  for a: Bool
  for b: Bool
  for h: T(bi(a, b))
  for hb: T(b)
  T(a)

def bi.rl(a, b, h, hb):
  match a b:
    case False{} False{}:
      false.elim(T(False{}), hb)
    case False{} True{}:
      false.elim(T(False{}), h)
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law bi.i:
  for a: Bool
  for b: Bool
  for f: T(a) -> T(b)
  for k: T(b) -> T(a)
  T(bi(a, b))

def bi.i(a, b, f, k):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      k({==})
    case True{} False{}:
      f({==})
    case True{} True{}:
      {==}

law not.t:
  for a: Bool
  for h: T(Bool.not(a))
  for ha: T(a)
  Empty

def not.t(a, h, ha):
  match a:
    case False{}:
      false.empty(ha)
    case True{}:
      false.empty(h)

law imp.e:
  for a: Bool
  for -b: Bool
  for h: T(imp.b(a, b))
  for ha: T(a)
  T(b)

def imp.e(a, b, h, ha):
  match a:
    case False{}:
      false.elim(T(b), ha)
    case True{}:
      h

law imp.i:
  for a: Bool
  for -b: Bool
  for f: T(a) -> T(b)
  T(imp.b(a, b))

def imp.i(a, b, f):
  match a:
    case False{}:
      {==}
    case True{}:
      f({==})

# ---- positions ----

def END() -> U32:
  4294967295

def code(c: Char) -> U32:
  Char.to_u32(c)

# at(c, x, i): reading the input from cell i spells x and then the end marker.
def at(+c: Cx, x: String, +i: U32) -> Bool:
  match x:
    case SNil{}:
      U32.is_eq(rdA(c, i), END)
    case SCon{+h, t}:
      Bool.and(Bool.and(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END))), at(c, t, (i + 1 : U32)))

law eq.trans3:
  for u: U32
  for v: U32
  for +w: U32
  for e1: T(U32.is_eq(u, w))
  for e2: T(U32.is_eq(u, v))
  T(U32.is_eq(v, w))

def eq.trans3(u, v, w, e1, e2):
  %u32.eq.t(u, v, e2) : {U32.is_eq(_, w) == True{} : Bool}
  e1

law end.ne:
  for +u: U32
  for +h: Char
  for e1: T(U32.is_eq(u, END))
  for e2: T(U32.is_eq(u, code(h)))
  for n: T(Bool.not(U32.is_eq(code(h), END)))
  Empty

def end.ne(u, h, e1, e2, n):
  not.t(U32.is_eq(code(h), END), n, eq.trans3(u, code(h), END, e1, e2))

law at.head:
  for +c: Cx
  for +h: Char
  for -t: String
  for +i: U32
  for hx: T(at(c, SCon{h, t}, i))
  T(U32.is_eq(rdA(c, i), code(h)))

def at.head(c, h, t, i, hx):
  and.l(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END)), and.l(Bool.and(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END))), at(c, t, (i + 1 : U32)), hx))

law at.nend:
  for +c: Cx
  for +h: Char
  for -t: String
  for +i: U32
  for hx: T(at(c, SCon{h, t}, i))
  T(Bool.not(U32.is_eq(code(h), END)))

def at.nend(c, h, t, i, hx):
  and.r(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END)), and.l(Bool.and(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END))), at(c, t, (i + 1 : U32)), hx))

law at.tail:
  for +c: Cx
  for +h: Char
  for +t: String
  for +i: U32
  for hx: T(at(c, SCon{h, t}, i))
  T(at(c, t, (i + 1 : U32)))

def at.tail(c, h, t, i, hx):
  and.r(Bool.and(U32.is_eq(rdA(c, i), code(h)), Bool.not(U32.is_eq(code(h), END))), at(c, t, (i + 1 : U32)), hx)

law code.eq:
  for a: Char
  for b: Char
  for h: {code(a) == code(b) : U32}
  {a == b : Char}

def code.eq(a, b, h):
  match a b:
    case Chr{x} Chr{y}:
      %h : {Chr{x} == Chr{_} : Char}
      {==}

law at.inj.c:
  for -h1: Char
  for -h2: Char
  for -t1: String
  for -t2: String
  for e1: {h1 == h2 : Char}
  for e2: {t1 == t2 : String}
  {SCon{h1, t1} == SCon{h2, t2} : String}

def at.inj.c(h1, h2, t1, t2, e1, e2):
  %e1 : {SCon{h1, t1} == SCon{_, t2} : String}
  %e2 : {SCon{h1, t1} == SCon{h1, _} : String}
  {==}

law at.inj:
  for +c: Cx
  for x: String
  for y: String
  for +i: U32
  for +hx: T(at(c, x, i))
  for +hy: T(at(c, y, i))
  {x == y : String}

def at.inj(c, x, y, i, hx, hy):
  match x y:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+h, +t}:
      absurd({SNil{} == SCon{h, t} : String}, end.ne(rdA(c, i), h, hx, at.head(c, h, t, i, hy), at.nend(c, h, t, i, hy)))
    case SCon{+h, +t} SNil{}:
      absurd({SCon{h, t} == SNil{} : String}, end.ne(rdA(c, i), h, hy, at.head(c, h, t, i, hx), at.nend(c, h, t, i, hx)))
    case SCon{+h1, +t1} SCon{+h2, +t2}:
      at.inj.c(h1, h2, t1, t2, code.eq(h1, h2, u32.eq.t(code(h1), code(h2), eq.trans3(rdA(c, i), code(h1), code(h2), at.head(c, h2, t2, i, hy), at.head(c, h1, t1, i, hx)))), at.inj(c, t1, t2, (i + 1 : U32), at.tail(c, h1, t1, i, hx), at.tail(c, h2, t2, i, hy)))

# ---- sets of cells ----

def sub(a: UL, +b: UL) -> Bool:
  match a:
    case UNil{}:
      True{}
    case UCon{+x, t}:
      Bool.and(has(x, b), sub(t, b))

def same(+a: UL, +b: UL) -> Bool:
  Bool.and(sub(a, b), sub(b, a))

law u32.eq.sym:
  for +a: U32
  for +b: U32
  for +h: T(U32.is_eq(a, b))
  T(U32.is_eq(b, a))

def u32.eq.sym(a, b, h):
  %u32.eq.t(a, b, h) : {U32.is_eq(_, a) == True{} : Bool}
  u32.refl(a)

law has.head:
  for +z: U32
  for +h: U32
  for -t: UL
  for +e: T(U32.is_eq(h, z))
  T(has(z, UCon{h, t}))

def has.head(z, h, t, e):
  or.l(U32.is_eq(h, z), has(z, t), e)

law has.self:
  for +z: U32
  for -t: UL
  T(has(z, UCon{z, t}))

def has.self(z, t):
  has.head(z, z, t, u32.refl(z))

law has.tail:
  for +z: U32
  for h: U32
  for +t: UL
  for +e: T(has(z, t))
  T(has(z, UCon{h, t}))

def has.tail(z, h, t, e):
  or.r(U32.is_eq(h, z), has(z, t), e)

law tr.u:
  for x: U32
  for z: U32
  for +b: UL
  for +e: T(U32.is_eq(x, z))
  for +h: T(has(x, b))
  T(has(z, b))

def tr.u(x, z, b, e, h):
  %u32.eq.t(x, z, e) : {has(_, b) == True{} : Bool}
  h

law sub.has:
  for +z: U32
  for +a: UL
  for +b: UL
  for +s: T(sub(a, b))
  for +h: T(has(z, a))
  T(has(z, b))

def sub.has(z, a, b, s, h):
  match a:
    case UNil{}:
      false.elim(T(has(z, b)), h)
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, z), has(z, t), T(has(z, b)), h, e => tr.u(x, z, b, e, and.l(has(x, b), sub(t, b), s)), +h2 => sub.has(z, t, b, and.r(has(x, b), sub(t, b), s), h2))

law sub.cons:
  for +x: U32
  for -t: UL
  for +b: UL
  for +h1: T(has(x, b))
  for +h2: T(sub(t, b))
  T(sub(UCon{x, t}, b))

def sub.cons(x, t, b, h1, h2):
  and.i(has(x, b), sub(t, b), h1, h2)

law sub.head:
  for +x: U32
  for -t: UL
  for +b: UL
  for +h: T(sub(UCon{x, t}, b))
  T(has(x, b))

def sub.head(x, t, b, h):
  and.l(has(x, b), sub(t, b), h)

law sub.tail:
  for +x: U32
  for +t: UL
  for +b: UL
  for +h: T(sub(UCon{x, t}, b))
  T(sub(t, b))

def sub.tail(x, t, b, h):
  and.r(has(x, b), sub(t, b), h)

law sub.weak:
  for a: UL
  for +x: U32
  for +b: UL
  for +h: T(sub(a, b))
  T(sub(a, UCon{x, b}))

def sub.weak(a, x, b, h):
  match a:
    case UNil{}:
      {==}
    case UCon{+y, +t}:
      sub.cons(y, t, UCon{x, b}, has.tail(y, x, b, sub.head(y, t, b, h)), sub.weak(t, x, b, sub.tail(y, t, b, h)))

law sub.refl:
  for a: UL
  T(sub(a, a))

def sub.refl(a):
  match a:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, UCon{x, t}, has.self(x, t), sub.weak(t, x, t, sub.refl(t)))

law sub.trans:
  for a: UL
  for +b: UL
  for +c: UL
  for +s1: T(sub(a, b))
  for +s2: T(sub(b, c))
  T(sub(a, c))

def sub.trans(a, b, c, s1, s2):
  match a:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, c, sub.has(x, b, c, s2, sub.head(x, t, b, s1)), sub.trans(t, b, c, sub.tail(x, t, b, s1), s2))

law same.l:
  for +a: UL
  for +b: UL
  for +h: T(same(a, b))
  T(sub(a, b))

def same.l(a, b, h):
  and.l(sub(a, b), sub(b, a), h)

law same.r:
  for +a: UL
  for +b: UL
  for +h: T(same(a, b))
  T(sub(b, a))

def same.r(a, b, h):
  and.r(sub(a, b), sub(b, a), h)

law same.i:
  for +a: UL
  for +b: UL
  for +h1: T(sub(a, b))
  for +h2: T(sub(b, a))
  T(same(a, b))

def same.i(a, b, h1, h2):
  and.i(sub(a, b), sub(b, a), h1, h2)

law same.refl:
  for +a: UL
  T(same(a, a))

def same.refl(a):
  same.i(a, a, sub.refl(a), sub.refl(a))

law same.trans:
  for +a: UL
  for +b: UL
  for +c: UL
  for +h1: T(same(a, b))
  for +h2: T(same(b, c))
  T(same(a, c))

def same.trans(a, b, c, h1, h2):
  same.i(a, c, sub.trans(a, b, c, same.l(a, b, h1), same.l(b, c, h2)), sub.trans(c, b, a, same.r(b, c, h2), same.r(a, b, h1)))

# ---- list operations keep membership ----

law uapp.sub:
  for a: UL
  for b: UL
  for +c: UL
  for +h1: T(sub(a, c))
  for +h2: T(sub(b, c))
  T(sub(uapp(a, b), c))

def uapp.sub(a, b, c, h1, h2):
  match a:
    case UNil{}:
      h2
    case UCon{+x, +t}:
      sub.cons(x, uapp(t, b), c, sub.head(x, t, c, h1), uapp.sub(t, b, c, sub.tail(x, t, c, h1), h2))

law uapp.in.l:
  for +z: U32
  for +a: UL
  for +b: UL
  for +h: T(has(z, a))
  T(has(z, uapp(a, b)))

def uapp.in.l(z, a, b, h):
  match a:
    case UNil{}:
      false.elim(T(has(z, b)), h)
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, z), has(z, t), T(has(z, UCon{x, uapp(t, b)})), h, e => has.head(z, x, uapp(t, b), e), +h2 => has.tail(z, x, uapp(t, b), uapp.in.l(z, t, b, h2)))

law uapp.in.r:
  for +z: U32
  for +a: UL
  for +b: UL
  for +h: T(has(z, b))
  T(has(z, uapp(a, b)))

def uapp.in.r(z, a, b, h):
  match a:
    case UNil{}:
      h
    case UCon{+x, +t}:
      has.tail(z, x, uapp(t, b), uapp.in.r(z, t, b, h))

law uapp.or:
  for +z: U32
  for +a: UL
  for +b: UL
  for +H: T(has(z, uapp(a, b)))
  T(Bool.or(has(z, a), has(z, b)))

def uapp.or(z, a, b, H):
  match a:
    case UNil{}:
      H
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, z), has(z, uapp(t, b)), T(Bool.or(Bool.or(U32.is_eq(x, z), has(z, t)), has(z, b))), H, e => or.l(Bool.or(U32.is_eq(x, z), has(z, t)), has(z, b), or.l(U32.is_eq(x, z), has(z, t), e)), +h2 => or.c(has(z, t), has(z, b), T(Bool.or(Bool.or(U32.is_eq(x, z), has(z, t)), has(z, b))), uapp.or(z, t, b, h2), h3 => or.l(Bool.or(U32.is_eq(x, z), has(z, t)), has(z, b), or.r(U32.is_eq(x, z), has(z, t), h3)), h4 => or.r(Bool.or(U32.is_eq(x, z), has(z, t)), has(z, b), h4)))

law sub.uapp.l:
  for l: UL
  for +a: UL
  for +b: UL
  for +h: T(sub(l, a))
  T(sub(l, uapp(a, b)))

def sub.uapp.l(l, a, b, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, uapp(a, b), uapp.in.l(x, a, b, sub.head(x, t, a, h)), sub.uapp.l(t, a, b, sub.tail(x, t, a, h)))

law sub.uapp.r:
  for l: UL
  for +a: UL
  for +b: UL
  for +h: T(sub(l, b))
  T(sub(l, uapp(a, b)))

def sub.uapp.r(l, a, b, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, uapp(a, b), uapp.in.r(x, a, b, sub.head(x, t, b, h)), sub.uapp.r(t, a, b, sub.tail(x, t, b, h)))

# merge

law merge.sub.go:
  for +f: Nat
  for o: Cmp
  for +x: U32
  for +y: U32
  for xt: UL
  for yt: UL
  for +c: UL
  for +hx: T(has(x, c))
  for +hy: T(has(y, c))
  for +hxt: T(sub(xt, c))
  for +hyt: T(sub(yt, c))
  T(sub(merge.go(f, o, x, y, xt, yt), c))

def merge.sub.go(f, o, x, y, xt, yt, c, hx, hy, hxt, hyt):
  match f:
    case 0n:
      sub.cons(x, UCon{y, uapp(xt, yt)}, c, hx, sub.cons(y, uapp(xt, yt), c, hy, uapp.sub(xt, yt, c, hxt, hyt)))
    case 1n+g:
      match o:
        case LT{}:
          match xt:
            case UNil{}:
              sub.cons(x, UCon{y, yt}, c, hx, sub.cons(y, yt, c, hy, hyt))
            case UCon{+x2, +xt2}:
              sub.cons(x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), c, hx, merge.sub.go(g, U32.cmp(x2, y), x2, y, xt2, yt, c, sub.head(x2, xt2, c, hxt), hy, sub.tail(x2, xt2, c, hxt), hyt))
        case EQ{}:
          match xt:
            case UNil{}:
              sub.cons(x, yt, c, hx, hyt)
            case UCon{+x2, +xt2}:
              match yt:
                case UNil{}:
                  sub.cons(x, UCon{x2, xt2}, c, hx, hxt)
                case UCon{+y2, +yt2}:
                  sub.cons(x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2), c, hx, merge.sub.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2, c, sub.head(x2, xt2, c, hxt), sub.head(y2, yt2, c, hyt), sub.tail(x2, xt2, c, hxt), sub.tail(y2, yt2, c, hyt)))
        case GT{}:
          match yt:
            case UNil{}:
              sub.cons(y, UCon{x, xt}, c, hy, sub.cons(x, xt, c, hx, hxt))
            case UCon{+y2, +yt2}:
              sub.cons(y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2), c, hy, merge.sub.go(g, U32.cmp(x, y2), x, y2, xt, yt2, c, hx, sub.head(y2, yt2, c, hyt), hxt, sub.tail(y2, yt2, c, hyt)))

law merge.sub:
  for a: UL
  for b: UL
  for +c: UL
  for +h1: T(sub(a, c))
  for +h2: T(sub(b, c))
  T(sub(merge(a, b), c))

def merge.sub(a, b, c, h1, h2):
  match a:
    case UNil{}:
      h2
    case UCon{+x, +xt}:
      match b:
        case UNil{}:
          h1
        case UCon{+y, +yt}:
          merge.sub.go(4294967295n, U32.cmp(x, y), x, y, xt, yt, c, sub.head(x, xt, c, h1), sub.head(y, yt, c, h2), sub.tail(x, xt, c, h1), sub.tail(y, yt, c, h2))

# cells of a merge: every element of an input is in the output

def inm(+z: U32, +x: U32, +y: U32, +xt: UL, +yt: UL) -> Bool:
  Bool.or(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)))

law inm.x:
  for +z: U32
  for +x: U32
  for +y: U32
  for +xt: UL
  for +yt: UL
  for +h: T(U32.is_eq(x, z))
  T(inm(z, x, y, xt, yt))

def inm.x(z, x, y, xt, yt, h):
  or.l(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)), or.l(U32.is_eq(x, z), U32.is_eq(y, z), h))

law inm.y:
  for +z: U32
  for +x: U32
  for +y: U32
  for +xt: UL
  for +yt: UL
  for +h: T(U32.is_eq(y, z))
  T(inm(z, x, y, xt, yt))

def inm.y(z, x, y, xt, yt, h):
  or.l(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)), or.r(U32.is_eq(x, z), U32.is_eq(y, z), h))

law inm.xt:
  for +z: U32
  for +x: U32
  for +y: U32
  for +xt: UL
  for +yt: UL
  for +h: T(has(z, xt))
  T(inm(z, x, y, xt, yt))

def inm.xt(z, x, y, xt, yt, h):
  or.r(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)), or.l(has(z, xt), has(z, yt), h))

law inm.yt:
  for +z: U32
  for +x: U32
  for +y: U32
  for +xt: UL
  for +yt: UL
  for +h: T(has(z, yt))
  T(inm(z, x, y, xt, yt))

def inm.yt(z, x, y, xt, yt, h):
  or.r(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)), or.r(has(z, xt), has(z, yt), h))

def inm.c(+z: U32, +x: U32, +y: U32, +xt: UL, +yt: UL, -C: Type, H: T(inm(z, x, y, xt, yt)), a: T(U32.is_eq(x, z)) -> C, b: T(U32.is_eq(y, z)) -> C, d: T(has(z, xt)) -> C, e: T(has(z, yt)) -> C) -> C:
  or.c(Bool.or(U32.is_eq(x, z), U32.is_eq(y, z)), Bool.or(has(z, xt), has(z, yt)), C, H, h1 => or.c(U32.is_eq(x, z), U32.is_eq(y, z), C, h1, a, b), h2 => or.c(has(z, xt), has(z, yt), C, h2, d, e))

law cmp.eq.u:
  for +x: U32
  for +y: U32
  for -o: Cmp
  for e1: {o == U32.cmp(x, y) : Cmp}
  for e2: {o == EQ{} : Cmp}
  T(U32.is_eq(x, y))

def cmp.eq.u(x, y, o, e1, e2):
  %Equal.trans(Cmp, EQ{}, o, U32.cmp(x, y), Equal.sym(Cmp, o, EQ{}, e2), e1) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

law eq.tr2:
  for x: U32
  for y: U32
  for +z: U32
  for +e1: T(U32.is_eq(x, y))
  for +e2: T(U32.is_eq(y, z))
  T(U32.is_eq(x, z))

def eq.tr2(x, y, z, e1, e2):
  %Equal.sym(U32, x, y, u32.eq.t(x, y, e1)) : {U32.is_eq(_, z) == True{} : Bool}
  e2

law merge.in.go:
  for +f: Nat
  for o: Cmp
  for +x: U32
  for +y: U32
  for +xt: UL
  for +yt: UL
  for +z: U32
  for +e: {o == U32.cmp(x, y) : Cmp}
  for +h: T(inm(z, x, y, xt, yt))
  T(has(z, merge.go(f, o, x, y, xt, yt)))

def merge.in.go(f, o, x, y, xt, yt, z, e, h):
  match f:
    case 0n:
      inm.c(z, x, y, xt, yt, T(has(z, UCon{x, UCon{y, uapp(xt, yt)}})), h, ex => has.head(z, x, UCon{y, uapp(xt, yt)}, ex), ey => has.tail(z, x, UCon{y, uapp(xt, yt)}, has.head(z, y, uapp(xt, yt), ey)), +hx => has.tail(z, x, UCon{y, uapp(xt, yt)}, has.tail(z, y, uapp(xt, yt), uapp.in.l(z, xt, yt, hx))), +hy => has.tail(z, x, UCon{y, uapp(xt, yt)}, has.tail(z, y, uapp(xt, yt), uapp.in.r(z, xt, yt, hy))))
    case 1n+g:
      match o:
        case LT{}:
          match xt:
            case UNil{}:
              inm.c(z, x, y, UNil{}, yt, T(has(z, UCon{x, UCon{y, yt}})), h, ex => has.head(z, x, UCon{y, yt}, ex), ey => has.tail(z, x, UCon{y, yt}, has.head(z, y, yt, ey)), hn => false.elim(T(has(z, UCon{x, UCon{y, yt}})), hn), +hy => has.tail(z, x, UCon{y, yt}, has.tail(z, y, yt, hy)))
            case UCon{+x2, +xt2}:
              inm.c(z, x, y, UCon{x2, xt2}, yt, T(has(z, UCon{x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt)})), h, ex => has.head(z, x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), ex), +ey => has.tail(z, x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), merge.in.go(g, U32.cmp(x2, y), x2, y, xt2, yt, z, {==}, inm.y(z, x2, y, xt2, yt, ey))), +hx => or.c(U32.is_eq(x2, z), has(z, xt2), T(has(z, UCon{x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt)})), hx, +e2 => has.tail(z, x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), merge.in.go(g, U32.cmp(x2, y), x2, y, xt2, yt, z, {==}, inm.x(z, x2, y, xt2, yt, e2))), +h2 => has.tail(z, x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), merge.in.go(g, U32.cmp(x2, y), x2, y, xt2, yt, z, {==}, inm.xt(z, x2, y, xt2, yt, h2)))), +hy => has.tail(z, x, merge.go(g, U32.cmp(x2, y), x2, y, xt2, yt), merge.in.go(g, U32.cmp(x2, y), x2, y, xt2, yt, z, {==}, inm.yt(z, x2, y, xt2, yt, hy))))
        case EQ{}:
          match xt:
            case UNil{}:
              inm.c(z, x, y, UNil{}, yt, T(has(z, UCon{x, yt})), h, ex => has.head(z, x, yt, ex), ey => has.head(z, x, yt, eq.tr2(x, y, z, cmp.eq.u(x, y, EQ{}, e, {==}), ey)), hn => false.elim(T(has(z, UCon{x, yt})), hn), +hy => has.tail(z, x, yt, hy))
            case UCon{+x2, +xt2}:
              match yt:
                case UNil{}:
                  inm.c(z, x, y, UCon{x2, xt2}, UNil{}, T(has(z, UCon{x, UCon{x2, xt2}})), h, ex => has.head(z, x, UCon{x2, xt2}, ex), ey => has.head(z, x, UCon{x2, xt2}, eq.tr2(x, y, z, cmp.eq.u(x, y, EQ{}, e, {==}), ey)), +hx => has.tail(z, x, UCon{x2, xt2}, hx), hn => false.elim(T(has(z, UCon{x, UCon{x2, xt2}})), hn))
                case UCon{+y2, +yt2}:
                  inm.c(z, x, y, UCon{x2, xt2}, UCon{y2, yt2}, T(has(z, UCon{x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2)})), h, ex => has.head(z, x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2), ex), ey => has.head(z, x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2), eq.tr2(x, y, z, cmp.eq.u(x, y, EQ{}, e, {==}), ey)), +hx => has.tail(z, x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2), or.c(U32.is_eq(x2, z), has(z, xt2), T(has(z, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2))), hx, +e2 => merge.in.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2, z, {==}, inm.x(z, x2, y2, xt2, yt2, e2)), +h2 => merge.in.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2, z, {==}, inm.xt(z, x2, y2, xt2, yt2, h2)))), +hy => has.tail(z, x, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2), or.c(U32.is_eq(y2, z), has(z, yt2), T(has(z, merge.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2))), hy, +e2 => merge.in.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2, z, {==}, inm.y(z, x2, y2, xt2, yt2, e2)), +h2 => merge.in.go(g, U32.cmp(x2, y2), x2, y2, xt2, yt2, z, {==}, inm.yt(z, x2, y2, xt2, yt2, h2)))))
        case GT{}:
          match yt:
            case UNil{}:
              inm.c(z, x, y, xt, UNil{}, T(has(z, UCon{y, UCon{x, xt}})), h, ex => has.tail(z, y, UCon{x, xt}, has.head(z, x, xt, ex)), ey => has.head(z, y, UCon{x, xt}, ey), +hx => has.tail(z, y, UCon{x, xt}, has.tail(z, x, xt, hx)), hn => false.elim(T(has(z, UCon{y, UCon{x, xt}})), hn))
            case UCon{+y2, +yt2}:
              inm.c(z, x, y, xt, UCon{y2, yt2}, T(has(z, UCon{y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2)})), h, +ex => has.tail(z, y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2), merge.in.go(g, U32.cmp(x, y2), x, y2, xt, yt2, z, {==}, inm.x(z, x, y2, xt, yt2, ex))), ey => has.head(z, y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2), ey), +hx => has.tail(z, y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2), merge.in.go(g, U32.cmp(x, y2), x, y2, xt, yt2, z, {==}, inm.xt(z, x, y2, xt, yt2, hx))), +hy => has.tail(z, y, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2), or.c(U32.is_eq(y2, z), has(z, yt2), T(has(z, merge.go(g, U32.cmp(x, y2), x, y2, xt, yt2))), hy, +e2 => merge.in.go(g, U32.cmp(x, y2), x, y2, xt, yt2, z, {==}, inm.y(z, x, y2, xt, yt2, e2)), +h2 => merge.in.go(g, U32.cmp(x, y2), x, y2, xt, yt2, z, {==}, inm.yt(z, x, y2, xt, yt2, h2)))))

law merge.in.l:
  for +z: U32
  for +a: UL
  for +b: UL
  for +h: T(has(z, a))
  T(has(z, merge(a, b)))

def merge.in.l(z, a, b, h):
  match a:
    case UNil{}:
      false.elim(T(has(z, merge(UNil{}, b))), h)
    case UCon{+x, +xt}:
      match b:
        case UNil{}:
          h
        case UCon{+y, +yt}:
          or.c(U32.is_eq(x, z), has(z, xt), T(has(z, merge.go(4294967295n, U32.cmp(x, y), x, y, xt, yt))), h, +e => merge.in.go(4294967295n, U32.cmp(x, y), x, y, xt, yt, z, {==}, inm.x(z, x, y, xt, yt, e)), +h2 => merge.in.go(4294967295n, U32.cmp(x, y), x, y, xt, yt, z, {==}, inm.xt(z, x, y, xt, yt, h2)))

law merge.in.r:
  for +z: U32
  for +a: UL
  for +b: UL
  for +h: T(has(z, b))
  T(has(z, merge(a, b)))

def merge.in.r(z, a, b, h):
  match a:
    case UNil{}:
      h
    case UCon{+x, +xt}:
      match b:
        case UNil{}:
          false.elim(T(has(z, merge(UCon{x, xt}, UNil{}))), h)
        case UCon{+y, +yt}:
          or.c(U32.is_eq(y, z), has(z, yt), T(has(z, merge.go(4294967295n, U32.cmp(x, y), x, y, xt, yt))), h, +e => merge.in.go(4294967295n, U32.cmp(x, y), x, y, xt, yt, z, {==}, inm.y(z, x, y, xt, yt, e)), +h2 => merge.in.go(4294967295n, U32.cmp(x, y), x, y, xt, yt, z, {==}, inm.yt(z, x, y, xt, yt, h2)))

law sub.merge.l:
  for l: UL
  for +a: UL
  for +b: UL
  for +h: T(sub(l, a))
  T(sub(l, merge(a, b)))

def sub.merge.l(l, a, b, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, merge(a, b), merge.in.l(x, a, b, sub.head(x, t, a, h)), sub.merge.l(t, a, b, sub.tail(x, t, a, h)))

law sub.merge.r:
  for l: UL
  for +a: UL
  for +b: UL
  for +h: T(sub(l, b))
  T(sub(l, merge(a, b)))

def sub.merge.r(l, a, b, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, merge(a, b), merge.in.r(x, a, b, sub.head(x, t, b, h)), sub.merge.r(t, a, b, sub.tail(x, t, b, h)))

# merge is the union, as a set
law merge.same:
  for +a: UL
  for +b: UL
  T(same(merge(a, b), uapp(a, b)))

def merge.same(a, b):
  same.i(merge(a, b), uapp(a, b), merge.sub(a, b, uapp(a, b), sub.uapp.l(a, a, b, sub.refl(a)), sub.uapp.r(b, a, b, sub.refl(b))), uapp.sub(a, b, merge(a, b), sub.merge.l(a, a, b, sub.refl(a)), sub.merge.r(b, a, b, sub.refl(b))))

# rev

law rev.go.sub:
  for l: UL
  for acc: UL
  for +c: UL
  for +h1: T(sub(l, c))
  for +h2: T(sub(acc, c))
  T(sub(rev.go(l, acc), c))

def rev.go.sub(l, acc, c, h1, h2):
  match l:
    case UNil{}:
      h2
    case UCon{+x, +t}:
      rev.go.sub(t, UCon{x, acc}, c, sub.tail(x, t, c, h1), sub.cons(x, acc, c, sub.head(x, t, c, h1), h2))

law rev.go.in.acc:
  for l: UL
  for +acc: UL
  for +z: U32
  for +h: T(has(z, acc))
  T(has(z, rev.go(l, acc)))

def rev.go.in.acc(l, acc, z, h):
  match l:
    case UNil{}:
      h
    case UCon{+x, +t}:
      rev.go.in.acc(t, UCon{x, acc}, z, has.tail(z, x, acc, h))

law rev.go.in.l:
  for l: UL
  for +acc: UL
  for +z: U32
  for +h: T(has(z, l))
  T(has(z, rev.go(l, acc)))

def rev.go.in.l(l, acc, z, h):
  match l:
    case UNil{}:
      false.elim(T(has(z, rev.go(UNil{}, acc))), h)
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, z), has(z, t), T(has(z, rev.go(t, UCon{x, acc}))), h, e => rev.go.in.acc(t, UCon{x, acc}, z, has.head(z, x, acc, e)), +h2 => rev.go.in.l(t, UCon{x, acc}, z, h2))

law sub.rev:
  for l: UL
  for +a: UL
  for +h: T(sub(l, a))
  T(sub(l, rev(a)))

def sub.rev(l, a, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, rev(a), rev.go.in.l(a, UNil{}, x, sub.head(x, t, a, h)), sub.rev(t, a, sub.tail(x, t, a, h)))

law rev.same:
  for +a: UL
  T(same(rev(a), a))

def rev.same(a):
  same.i(rev(a), a, rev.go.sub(a, UNil{}, a, sub.refl(a), {==}), sub.rev(a, a, sub.refl(a)))

# vnorm, and what a result value means

def ex(+f: UL, v: V) -> Bool:
  match v:
    case VStuck{}:
      True{}
    case VEnds{e}:
      same(e, f)
    case VOne{+x}:
      same(UCon{x, UNil{}}, f)
    case _:
      False{}

law ex.vnorm:
  for e: UL
  for +f: UL
  for +h: T(same(e, f))
  T(ex(f, vnorm(e)))

def ex.vnorm(e, f, h):
  match e:
    case UNil{}:
      h
    case UCon{+x, +t}:
      match t:
        case UNil{}:
          h
        case UCon{+y, +r}:
          h

law ex.same:
  for +f: UL
  for +g: UL
  for v: V
  for +hs: T(same(f, g))
  for +h: T(ex(f, v))
  T(ex(g, v))

def ex.same(f, g, v, hs, h):
  match v:
    case VNone{}:
      false.elim(T(False{}), h)
    case VStuck{}:
      {==}
    case VEnds{+e}:
      same.trans(e, f, g, h, hs)
    case VOne{+x}:
      same.trans(UCon{x, UNil{}}, f, g, h, hs)
    case VNode{q, w}:
      false.elim(T(False{}), h)
# ---- cells ----

def pos.go(q: String, +i: U32) -> U32:
  match q:
    case SNil{}:
      i
    case SCon{h, t}:
      pos.go(t, (i + 1 : U32))

def pos(+i: U32, q: String) -> U32:
  pos.go(q, i)

def ifs(b: Bool, x: String, y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def cell.go(x: String, +n: U32, +z: U32) -> Bool:
  match x:
    case SNil{}:
      U32.is_eq(n, z)
    case SCon{h, t}:
      Bool.or(U32.is_eq(n, z), cell.go(t, (n + 1 : U32), z))

def suf.go(x: String, +n: U32, +z: U32) -> String:
  match x:
    case SNil{}:
      ""
    case SCon{+h, +t}:
      ifs(U32.is_eq(n, z), SCon{h, t}, suf.go(t, (n + 1 : U32), z))

def cell(+c: Cx, +z: U32) -> Bool:
  cell.go(cS(c), cnx(c), z)

def suf(+c: Cx, +z: U32) -> String:
  suf.go(cS(c), cnx(c), z)

def stail(x: String) -> String:
  match x:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

def isnil(x: String) -> Type:
  match x:
    case SNil{}:
      Unit
    case SCon{h, t}:
      Empty

law cons.ne.nil:
  for -h: Char
  for -t: String
  for e: {SCon{h, t} == SNil{} : String}
  Empty

def cons.ne.nil(h, t, e):
  %Equal.sym(String, SCon{h, t}, SNil{}, e) : isnil(_)
  Unit{}

law app.cons.eq:
  for +w: String
  for +h: Char
  for c: Char
  for t: String
  {SCon{h, (w ++ SCon{c, SNil{}}) ++ t} == SCon{h, w ++ SCon{c, t}} : String}

def app.cons.eq(w, h, c, t):
  match w:
    case SNil{}:
      {==}
    case SCon{+a, +b}:
      Equal.cong(String, String, s => SCon{h, s}, SCon{a, (b ++ SCon{c, SNil{}}) ++ t}, SCon{a, b ++ SCon{c, t}}, app.cons.eq(b, a, c, t))

law no.cyc:
  for y: String
  for +h: Char
  for w: String
  for e: {SCon{h, w ++ y} == y : String}
  Empty

def no.cyc(y, h, w, e):
  match y:
    case SNil{}:
      cons.ne.nil(h, w ++ SNil{}, e)
    case SCon{+c, +t}:
      match w:
        case SNil{}:
          no.cyc(t, c, SNil{}, Equal.cong(String, String, s => stail(s), SCon{h, SCon{c, t}}, SCon{c, t}, e))
        case SCon{+h2, +w2}:
          no.cyc(t, h2, w2 ++ SCon{c, SNil{}}, Equal.trans(String, SCon{h2, (w2 ++ SCon{c, SNil{}}) ++ t}, SCon{h2, w2 ++ SCon{c, t}}, t, app.cons.eq(w2, h2, c, t), Equal.cong(String, String, s => stail(s), SCon{h, SCon{h2, w2 ++ SCon{c, t}}}, SCon{c, t}, e)))

# reading the input past a prefix

law at.pos:
  for +c: Cx
  for q: String
  for +y: String
  for +i: U32
  for +h: T(at(c, q ++ y, i))
  T(at(c, y, pos(i, q)))

def at.pos(c, q, y, i, h):
  match q:
    case SNil{}:
      h
    case SCon{+a, +t}:
      at.pos(c, t, y, (i + 1 : U32), at.tail(c, a, t ++ y, i, h))

law pos.app:
  for a: String
  for b: String
  for +i: U32
  {pos(pos(i, a), b) == pos(i, a ++ b) : U32}

def pos.app(a, b, i):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      pos.app(t, b, (i + 1 : U32))

law suf.go.find:
  for +c: Cx
  for u: String
  for +y: String
  for +n: U32
  for +h: T(at(c, u ++ y, n))
  {suf.go(u ++ y, n, pos(n, u)) == y : String}

law cell.go.find:
  for +c: Cx
  for u: String
  for +y: String
  for +n: U32
  for +h: T(at(c, u ++ y, n))
  T(cell.go(u ++ y, n, pos(n, u)))

law ifs.false:
  for b: Bool
  for x: String
  for y: String
  for e: {b == False{} : Bool}
  {ifs(b, x, y) == y : String}

def ifs.false(b, x, y, e):
  %Equal.sym(Bool, b, False{}, e) : {ifs(_, x, y) == y : String}
  {==}

law cyc.at:
  for +c: Cx
  for y: String
  for +n: U32
  for +z: U32
  for +hb: T(U32.is_eq(n, z))
  for +h: T(at(c, y, z))
  T(at(c, y, n))

def cyc.at(c, y, n, z, hb, h):
  %u32.eq.t(z, n, u32.eq.sym(n, z, hb)) : {at(c, y, _) == True{} : Bool}
  h

law suf.self:
  for y: String
  for +n: U32
  {suf.go(y, n, n) == y : String}

def suf.self(y, n):
  match y:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, U32.is_eq(n, n), True{}, u32.refl(n)) : {ifs(_, SCon{h, t}, suf.go(t, (n + 1 : U32), n)) == SCon{h, t} : String}
      {==}

law cell.self:
  for y: String
  for +n: U32
  T(cell.go(y, n, n))

def cell.self(y, n):
  match y:
    case SNil{}:
      u32.refl(n)
    case SCon{+h, +t}:
      or.l(U32.is_eq(n, n), cell.go(t, (n + 1 : U32), n), u32.refl(n))

law or.right.f:
  for a: Bool
  for -b: Bool
  for +e: {a == False{} : Bool}
  for +h: T(Bool.or(a, b))
  T(b)

def or.right.f(a, b, e, h):
  match a:
    case False{}:
      h
    case True{}:
      absurd(T(b), true.not_false(e))

law at.cyc:
  for +c: Cx
  for +a: Char
  for +t: String
  for +y: String
  for +n: U32
  for +h: T(at(c, SCon{a, t ++ y}, n))
  for +hb: T(U32.is_eq(n, pos((n + 1 : U32), t)))
  Empty

def at.cyc(c, a, t, y, n, h, hb):
  no.cyc(y, a, t, at.inj(c, SCon{a, t ++ y}, y, n, h, cyc.at(c, y, n, pos((n + 1 : U32), t), hb, at.pos(c, t, y, (n + 1 : U32), at.tail(c, a, t ++ y, n, h)))))

def suf.go.find(c, u, y, n, h):
  match u:
    case SNil{}:
      suf.self(y, n)
    case SCon{+a, +t}:
      bool.split(U32.is_eq(n, pos((n + 1 : U32), t)), {suf.go(SCon{a, t} ++ y, n, pos(n, SCon{a, t})) == y : String}, +eb => absurd({suf.go(SCon{a, t} ++ y, n, pos(n, SCon{a, t})) == y : String}, at.cyc(c, a, t, y, n, h, eb)), +eb => Equal.trans(String, ifs(U32.is_eq(n, pos((n + 1 : U32), t)), SCon{a, t ++ y}, suf.go(t ++ y, (n + 1 : U32), pos((n + 1 : U32), t))), suf.go(t ++ y, (n + 1 : U32), pos((n + 1 : U32), t)), y, ifs.false(U32.is_eq(n, pos((n + 1 : U32), t)), SCon{a, t ++ y}, suf.go(t ++ y, (n + 1 : U32), pos((n + 1 : U32), t)), eb), suf.go.find(c, t, y, (n + 1 : U32), at.tail(c, a, t ++ y, n, h))))

def cell.go.find(c, u, y, n, h):
  match u:
    case SNil{}:
      cell.self(y, n)
    case SCon{+a, +t}:
      or.r(U32.is_eq(n, pos((n + 1 : U32), t)), cell.go(t ++ y, (n + 1 : U32), pos((n + 1 : U32), t)), cell.go.find(c, t, y, (n + 1 : U32), at.tail(c, a, t ++ y, n, h)))

# elimination: a cell of the input is some prefix away from the start, and its suffix is what comes after that prefix
def CellW(+c: Cx, +z: U32) -> Type:
  &u: String -> {u ++ suf(c, z) == cS(c) : String} & {pos(cnx(c), u) == z : U32}

def CellGo(x: String, +n: U32, +z: U32) -> Type:
  &u: String -> {u ++ suf.go(x, n, z) == x : String} & {pos(n, u) == z : U32}

law cell.elim.nil:
  for +n: U32
  for +z: U32
  for +h: T(U32.is_eq(n, z))
  CellGo(SNil{}, n, z)

def cell.elim.nil(n, z, h):
  ("", {==}, u32.eq.t(n, z, h))

law cell.elim.hit:
  for +a: Char
  for +t: String
  for +n: U32
  for +z: U32
  for +h: T(U32.is_eq(n, z))
  CellGo(SCon{a, t}, n, z)

law cell.elim.step:
  for +a: Char
  for +t: String
  for +n: U32
  for +z: U32
  for +he: {U32.is_eq(n, z) == False{} : Bool}
  for w: CellGo(t, (n + 1 : U32), z)
  CellGo(SCon{a, t}, n, z)

law step.eq:
  for +a: Char
  for +t: String
  for +n: U32
  for +z: U32
  for u: String
  for +he: {U32.is_eq(n, z) == False{} : Bool}
  for e1: {u ++ suf.go(t, (n + 1 : U32), z) == t : String}
  {SCon{a, u} ++ suf.go(SCon{a, t}, n, z) == SCon{a, t} : String}

def step.eq(a, t, n, z, u, he, e1):
  %Equal.sym(Bool, U32.is_eq(n, z), False{}, he) : {SCon{a, u} ++ ifs(_, SCon{a, t}, suf.go(t, (n + 1 : U32), z)) == SCon{a, t} : String}
  Equal.cong(String, String, s => SCon{a, s}, u ++ suf.go(t, (n + 1 : U32), z), t, e1)

law hit.eq:
  for +a: Char
  for +t: String
  for +n: U32
  for +z: U32
  for +h: T(U32.is_eq(n, z))
  {SNil{} ++ suf.go(SCon{a, t}, n, z) == SCon{a, t} : String}

def hit.eq(a, t, n, z, h):
  %Equal.sym(Bool, U32.is_eq(n, z), True{}, h) : {ifs(_, SCon{a, t}, suf.go(t, (n + 1 : U32), z)) == SCon{a, t} : String}
  {==}

def cell.elim.step(a, t, n, z, he, w):
  match w:
    case (+u, e1, e2):
      (SCon{a, u}, step.eq(a, t, n, z, u, he, e1), e2)

def cell.elim.hit(a, t, n, z, h):
  ("", hit.eq(a, t, n, z, h), u32.eq.t(n, z, h))

law cell.elim.go:
  for x: String
  for +n: U32
  for +z: U32
  for +h: T(cell.go(x, n, z))
  CellGo(x, n, z)

def cell.elim.go(x, n, z, h):
  match x:
    case SNil{}:
      cell.elim.nil(n, z, h)
    case SCon{+a, +t}:
      bool.split(U32.is_eq(n, z), CellGo(SCon{a, t}, n, z), +eb => cell.elim.hit(a, t, n, z, eb), +eb => cell.elim.step(a, t, n, z, eb, cell.elim.go(t, (n + 1 : U32), z, or.right.f(U32.is_eq(n, z), cell.go(t, (n + 1 : U32), z), eb, h))))

law cell.elim:
  for +c: Cx
  for +z: U32
  for +h: T(cell(c, z))
  CellW(c, z)

def cell.elim(c, z, h):
  cell.elim.go(cS(c), cnx(c), z, h)

# ---- moving along the input ----

def Glob(+c: Cx) -> Bool:
  at(c, cS(c), cnx(c))

law cell.rec.at:
  for +c: Cx
  for +u: String
  for +y: String
  for +ga: T(Glob(c))
  for +e: {u ++ y == cS(c) : String}
  T(at(c, u ++ y, cnx(c)))

def cell.rec.at(c, u, y, ga, e):
  %Equal.sym(String, u ++ y, cS(c), e) : {at(c, _, cnx(c)) == True{} : Bool}
  ga

law cell.rec.suf:
  for +c: Cx
  for +u: String
  for +y: String
  for +ga: T(Glob(c))
  for +e: {u ++ y == cS(c) : String}
  {suf(c, pos(cnx(c), u)) == y : String}

def cell.rec.suf(c, u, y, ga, e):
  %e : {suf.go(_, cnx(c), pos(cnx(c), u)) == y : String}
  suf.go.find(c, u, y, cnx(c), cell.rec.at(c, u, y, ga, e))

law cell.rec.cell:
  for +c: Cx
  for +u: String
  for +y: String
  for +ga: T(Glob(c))
  for +e: {u ++ y == cS(c) : String}
  T(cell(c, pos(cnx(c), u)))

def cell.rec.cell(c, u, y, ga, e):
  %e : {cell.go(_, cnx(c), pos(cnx(c), u)) == True{} : Bool}
  cell.go.find(c, u, y, cnx(c), cell.rec.at(c, u, y, ga, e))

# After q, from a cell whose suffix is q ++ y, the suffix is y.
def Adv(+c: Cx, +z: U32, -q: String, +y: String) -> Type:
  T(cell(c, pos(z, q))) & {suf(c, pos(z, q)) == y : String}

law pos.sh:
  for +c: Cx
  for +u: String
  for +q: String
  for -z: U32
  for +e2: {pos(cnx(c), u) == z : U32}
  {pos(cnx(c), u ++ q) == pos(z, q) : U32}

def pos.sh(c, u, q, z, e2):
  %pos.app(u, q, cnx(c)) : {_ == pos(z, q) : U32}
  %e2 : {pos(pos(cnx(c), u), q) == pos(_, q) : U32}
  {==}

law app.shift:
  for +u: String
  for +q: String
  for +y: String
  for -x: String
  for -s: String
  for +e1: {u ++ x == s : String}
  for +e2: {q ++ y == x : String}
  {(u ++ q) ++ y == s : String}

def app.shift(u, q, y, x, s, e1, e2):
  %app.assoc.sym(u, q, y) : {_ == s : String}
  %Equal.sym(String, q ++ y, x, e2) : {u ++ _ == s : String}
  e1

law adv.c.k:
  for +c: Cx
  for +u: String
  for +q: String
  for +y: String
  for -z: U32
  for -x: String
  for +ga: T(Glob(c))
  for +e1: {u ++ x == cS(c) : String}
  for +e2: {pos(cnx(c), u) == z : U32}
  for +e: {q ++ y == x : String}
  T(cell(c, pos(z, q)))

def adv.c.k(c, u, q, y, z, x, ga, e1, e2, e):
  %pos.sh(c, u, q, z, e2) : T(cell(c, _))
  cell.rec.cell(c, u ++ q, y, ga, app.shift(u, q, y, x, cS(c), e1, e))

law adv.s.k:
  for +c: Cx
  for +u: String
  for +q: String
  for +y: String
  for -z: U32
  for -x: String
  for +ga: T(Glob(c))
  for +e1: {u ++ x == cS(c) : String}
  for +e2: {pos(cnx(c), u) == z : U32}
  for +e: {q ++ y == x : String}
  {suf(c, pos(z, q)) == y : String}

def adv.s.k(c, u, q, y, z, x, ga, e1, e2, e):
  %pos.sh(c, u, q, z, e2) : {suf(c, _) == y : String}
  cell.rec.suf(c, u ++ q, y, ga, app.shift(u, q, y, x, cS(c), e1, e))

law adv.k:
  for +c: Cx
  for -z: U32
  for +q: String
  for +y: String
  for +ga: T(Glob(c))
  for +e: {q ++ y == suf(c, z) : String}
  for w: CellW(c, z)
  Adv(c, z, q, y)

def adv.k(c, z, q, y, ga, e, w):
  match w:
    case (+u, +e1, e2):
      +e3 = e2
      (adv.c.k(c, u, q, y, z, suf(c, z), ga, e1, e3, e), adv.s.k(c, u, q, y, z, suf(c, z), ga, e1, e3, e))

law adv:
  for +c: Cx
  for +z: U32
  for +q: String
  for +y: String
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +e: {q ++ y == suf(c, z) : String}
  Adv(c, z, q, y)

def adv(c, z, q, y, ga, hc, e):
  adv.k(c, z, q, y, ga, e, cell.elim(c, z, hc))

# ---- the exact end cells of a rule ----

def pickc(b: Bool, +i: U32, l: UL) -> UL:
  match b:
    case True{}:
      UCon{i, l}
    case False{}:
      l

def E.wk(+c: Cx, +r: R, x: String, +p: String, +i: U32) -> UL:
  match x:
    case SNil{}:
      pickc(TR(c, r, p), i, UNil{})
    case SCon{+h, t}:
      pickc(TR(c, r, p), i, E.wk(c, r, t, p ++ SCon{h, SNil{}}, (i + 1 : U32)))

def E.go(+c: Cx, +r: R, +p: String, x: String, +i: U32) -> UL:
  E.wk(c, r, x, p, i)

def E(+c: Cx, +r: R, +z: U32) -> UL:
  E.go(c, r, "", suf(c, z), z)

law pickc.tail:
  for +b: Bool
  for +i: U32
  for +l: UL
  for +z: U32
  for +h: T(has(z, l))
  T(has(z, pickc(b, i, l)))

def pickc.tail(b, i, l, z, h):
  match b:
    case True{}:
      has.tail(z, i, l, h)
    case False{}:
      h

law pickc.in:
  for +b: Bool
  for +i: U32
  for +l: UL
  for +h: T(b)
  T(has(i, pickc(b, i, l)))

def pickc.in(b, i, l, h):
  match b:
    case True{}:
      has.self(i, l)
    case False{}:
      false.elim(T(has(i, l)), h)

def pickc.c(b: Bool, +i: U32, +l: UL, +z: U32, -C: Type, H: T(has(z, pickc(b, i, l))), f: T(b) -> T(U32.is_eq(i, z)) -> C, k: T(has(z, l)) -> C) -> C:
  match b:
    case True{}:
      or.c(U32.is_eq(i, z), has(z, l), C, H, e => f({==}, e), k)
    case False{}:
      k(H)

def EW(+c: Cx, +r: R, +p: String, -x: String, +i: U32, +w: U32) -> Type:
  &q: String -> &y: String -> {q ++ y == x : String} & {pos(i, q) == w : U32} & T(TR(c, r, p ++ q))

law tr.tr:
  for +c: Cx
  for -r: R
  for -x: String
  for -y: String
  for +e: {x == y : String}
  for h: T(TR(c, r, x))
  T(TR(c, r, y))

def tr.tr(c, r, x, y, e, h):
  %e : T(TR(c, r, _))
  h

law E.elim.hit:
  for +c: Cx
  for +r: R
  for +p: String
  for +x: String
  for +i: U32
  for +w: U32
  for +hb: T(TR(c, r, p))
  for +e: T(U32.is_eq(i, w))
  EW(c, r, p, x, i, w)

def E.elim.hit(c, r, p, x, i, w, hb, e):
  ("", x, {==}, u32.eq.t(i, w, e), tr.tr(c, r, p, p ++ "", app.nil.sym(p), hb))

law E.elim.step:
  for +c: Cx
  for +r: R
  for +p: String
  for +a: Char
  for +t: String
  for +i: U32
  for +w: U32
  for hw: EW(c, r, p ++ SCon{a, SNil{}}, t, (i + 1 : U32), w)
  EW(c, r, p, SCon{a, t}, i, w)

def E.elim.step(c, r, p, a, t, i, w, hw):
  match hw:
    case (+q, +y, e1, e2, h1):
      (SCon{a, q}, y, Equal.cong(String, String, s => SCon{a, s}, q ++ y, t, e1), e2, tr.tr(c, r, (p ++ SCon{a, SNil{}}) ++ q, p ++ SCon{a, q}, app.assoc(p, SCon{a, SNil{}}, q), h1))

law E.elim:
  for +c: Cx
  for +r: R
  for +x: String
  for +p: String
  for +i: U32
  for +w: U32
  for +h: T(has(w, E.go(c, r, p, x, i)))
  EW(c, r, p, x, i, w)

def E.elim(c, r, x, p, i, w, h):
  match x:
    case SNil{}:
      pickc.c(TR(c, r, p), i, UNil{}, w, EW(c, r, p, SNil{}, i, w), h, +hb => +e => E.elim.hit(c, r, p, SNil{}, i, w, hb, e), hn => false.elim(EW(c, r, p, SNil{}, i, w), hn))
    case SCon{+a, +t}:
      pickc.c(TR(c, r, p), i, E.go(c, r, p ++ SCon{a, SNil{}}, t, (i + 1 : U32)), w, EW(c, r, p, SCon{a, t}, i, w), h, +hb => +e => E.elim.hit(c, r, p, SCon{a, t}, i, w, hb, e), +h2 => E.elim.step(c, r, p, a, t, i, w, E.elim(c, r, t, p ++ SCon{a, SNil{}}, (i + 1 : U32), w, h2)))

law E.intro.here:
  for +c: Cx
  for +r: R
  for +p: String
  for +y: String
  for +i: U32
  for +h: T(TR(c, r, p))
  T(has(i, E.go(c, r, p, y, i)))

def E.intro.here(c, r, p, y, i, h):
  match y:
    case SNil{}:
      pickc.in(TR(c, r, p), i, UNil{}, h)
    case SCon{+a, +t}:
      pickc.in(TR(c, r, p), i, E.go(c, r, p ++ SCon{a, SNil{}}, t, (i + 1 : U32)), h)

law E.intro:
  for +c: Cx
  for +r: R
  for +q: String
  for +p: String
  for +y: String
  for +i: U32
  for +h: T(TR(c, r, p ++ q))
  T(has(pos(i, q), E.go(c, r, p, q ++ y, i)))

def E.intro(c, r, q, p, y, i, h):
  match q:
    case SNil{}:
      E.intro.here(c, r, p, y, i, tr.tr(c, r, p ++ "", p, app.nil(p), h))
    case SCon{+a, +t}:
      pickc.tail(TR(c, r, p), i, E.go(c, r, p ++ SCon{a, SNil{}}, t ++ y, (i + 1 : U32)), pos((i + 1 : U32), t), E.intro(c, r, t, p ++ SCon{a, SNil{}}, y, (i + 1 : U32), tr.tr(c, r, p ++ SCon{a, t}, (p ++ SCon{a, SNil{}}) ++ t, app.assoc.sym(p, SCon{a, SNil{}}, t), h)))
# ---- concatenation, on cells ----

def U(+c: Cx, +b: R, l: UL) -> UL:
  match l:
    case UNil{}:
      UNil{}
    case UCon{+h, t}:
      uapp(E(c, b, h), U(c, b, t))

def Eeq(+c: Cx, +r: R, x: String, +z: U32, +w: U32) -> Data:
  T(has(w, E.go(c, r, "", x, z)))

law tr.Eeq:
  for +c: Cx
  for +r: R
  for -x: String
  for -y: String
  for +z: U32
  for +w: U32
  for +e: {x == y : String}
  for +h: Eeq(c, r, x, z, w)
  Eeq(c, r, y, z, w)

def tr.Eeq(c, r, x, y, z, w, e, h):
  %e : Eeq(c, r, _, z, w)
  h

law tr.ew:
  for +c: Cx
  for +b: R
  for +x: U32
  for +h: U32
  for +w: U32
  for +e: T(U32.is_eq(x, h))
  for +hw: T(has(w, E(c, b, h)))
  T(has(w, E(c, b, x)))

def tr.ew(c, b, x, h, w, e, hw):
  %u32.eq.t(h, x, u32.eq.sym(x, h, e)) : T(has(w, E(c, b, _)))
  hw

law U.in:
  for +c: Cx
  for +b: R
  for +l: UL
  for +h: U32
  for +w: U32
  for +hw: T(has(w, E(c, b, h)))
  for +hh: T(has(h, l))
  T(has(w, U(c, b, l)))

def U.in(c, b, l, h, w, hw, hh):
  match l:
    case UNil{}:
      false.elim(T(has(w, UNil{})), hh)
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, h), has(h, t), T(has(w, uapp(E(c, b, x), U(c, b, t)))), hh, +e => uapp.in.l(w, E(c, b, x), U(c, b, t), tr.ew(c, b, x, h, w, e, hw)), +h2 => uapp.in.r(w, E(c, b, x), U(c, b, t), U.in(c, b, t, h, w, hw, h2)))

def UW(+c: Cx, +b: R, +l: UL, +w: U32) -> Type:
  &h: U32 -> T(has(h, l)) & T(has(w, E(c, b, h)))

law U.elim.head:
  for +c: Cx
  for +b: R
  for +x: U32
  for +t: UL
  for +w: U32
  for +h: T(has(w, E(c, b, x)))
  UW(c, b, UCon{x, t}, w)

def U.elim.head(c, b, x, t, w, h):
  (x, has.self(x, t), h)

law U.elim.tail:
  for +c: Cx
  for +b: R
  for +x: U32
  for +t: UL
  for +w: U32
  for u: UW(c, b, t, w)
  UW(c, b, UCon{x, t}, w)

def U.elim.tail(c, b, x, t, w, u):
  match u:
    case (+h, h1, h2):
      (h, has.tail(h, x, t, h1), h2)

law U.elim:
  for +c: Cx
  for +b: R
  for +l: UL
  for +w: U32
  for +h: T(has(w, U(c, b, l)))
  UW(c, b, l, w)

def U.elim(c, b, l, w, h):
  match l:
    case UNil{}:
      false.elim(UW(c, b, UNil{}, w), h)
    case UCon{+x, +t}:
      or.c(has(w, E(c, b, x)), has(w, U(c, b, t)), UW(c, b, UCon{x, t}, w), uapp.or(w, E(c, b, x), U(c, b, t), h), +h1 => U.elim.head(c, b, x, t, w, h1), +h2 => U.elim.tail(c, b, x, t, w, U.elim(c, b, t, w, h2)))

law cat.down.k2:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +q: String
  for +y: String
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +e1: {q ++ y == suf(c, z) : String}
  for +e2: {pos(z, q) == w : U32}
  for k: CatW(1n+B0(c), cg(c), a, b, q, "")
  T(has(w, U(c, b, E(c, a, z))))

law tr.Ep:
  for +c: Cx
  for +r: R
  for -x: String
  for +z: U32
  for +w0: U32
  for +w: U32
  for +e: {w0 == w : U32}
  for +h: T(has(w0, E.go(c, r, "", x, z)))
  T(has(w, E.go(c, r, "", x, z)))

def tr.Ep(c, r, x, z, w0, w, e, h):
  %e : T(has(_, E.go(c, r, "", x, z)))
  h

law pos.cat:
  for +z: U32
  for +s1: String
  for +s2: String
  for +q: String
  for +w: U32
  for +e3: {s1 ++ s2 == q : String}
  for +e2: {pos(z, q) == w : U32}
  {pos(pos(z, s1), s2) == w : U32}

def pos.cat(z, s1, s2, q, w, e3, e2):
  %Equal.sym(U32, pos(pos(z, s1), s2), pos(z, s1 ++ s2), pos.app(s1, s2, z)) : {_ == w : U32}
  %Equal.sym(String, s1 ++ s2, q, e3) : {pos(z, _) == w : U32}
  e2

# s1 ++ (s2 ++ y) == suf z
law cat.k3:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +s1: String
  for +s2: String
  for +y: String
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +e4: {s1 ++ (s2 ++ y) == suf(c, z) : String}
  for +e5: {pos(pos(z, s1), s2) == w : U32}
  for +ha: T(TR(c, a, s1))
  for +hb: T(TR(c, b, s2))
  for ad: Adv(c, z, s1, s2 ++ y)
  T(has(w, U(c, b, E(c, a, z))))

def cat.k3(c, a, b, z, s1, s2, y, w, ga, hc, e4, e5, ha, hb, ad):
  match ad:
    case (hcm, es):
      U.in(c, b, E(c, a, z), pos(z, s1), w, tr.Ep(c, b, suf(c, pos(z, s1)), pos(z, s1), pos(pos(z, s1), s2), w, e5, tr.Eeq(c, b, s2 ++ y, suf(c, pos(z, s1)), pos(z, s1), pos(pos(z, s1), s2), Equal.sym(String, suf(c, pos(z, s1)), s2 ++ y, es), E.intro(c, b, s2, "", y, pos(z, s1), hb))), tr.Eeq(c, a, s1 ++ (s2 ++ y), suf(c, z), z, pos(z, s1), e4, E.intro(c, a, s1, "", s2 ++ y, z, ha)))

law cat.e4:
  for +s1: String
  for +s2: String
  for +y: String
  for +q: String
  for -x: String
  for +e3: {s1 ++ s2 == q : String}
  for +e1: {q ++ y == x : String}
  {s1 ++ (s2 ++ y) == x : String}

def cat.e4(s1, s2, y, q, x, e3, e1):
  %app.assoc(s1, s2, y) : {_ == x : String}
  %Equal.sym(String, s1 ++ s2, q, e3) : {_ ++ y == x : String}
  e1

def cat.down.k2(c, a, b, z, q, y, w, ga, hc, e1, e2, k):
  match k:
    case (+s1, +s2, e3, ha, hb):
      +e6 = e3
      cat.k3(c, a, b, z, s1, s2, y, w, ga, hc, cat.e4(s1, s2, y, q, suf(c, z), e6, e1), pos.cat(z, s1, s2, q, w, e6, e2), ha, hb, adv(c, z, s1, s2 ++ y, ga, hc, cat.e4(s1, s2, y, q, suf(c, z), e6, e1)))

law cat.down.k1:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for h: EW(c, Cat{a, b}, "", suf(c, z), z, w)
  T(has(w, U(c, b, E(c, a, z))))

def cat.down.k1(c, a, b, z, w, ga, hc, h):
  match h:
    case (+q, +y, +e1, e2, ht):
      cat.down.k2(c, a, b, z, q, y, w, ga, hc, e1, e2, cat.elim(1n+B0(c), cg(c), a, b, q, "", ht))

law cat.down:
  for l: UL
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hl: T(sub(l, E(c, Cat{a, b}, z)))
  T(sub(l, U(c, b, E(c, a, z))))

def cat.down(l, c, a, b, z, ga, hc, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, U(c, b, E(c, a, z)), cat.down.k1(c, a, b, z, w, ga, hc, E.elim(c, Cat{a, b}, suf(c, z), "", z, w, sub.head(w, t, E(c, Cat{a, b}, z), hl))), cat.down(t, c, a, b, z, ga, hc, sub.tail(w, t, E(c, Cat{a, b}, z), hl)))

# the other direction: composing matches

def Comp(+c: Cx, +a: R, +b: R, +r0: R) -> Type:
  @s1: String -> @s2: String -> T(TR(c, a, s1)) -> T(TR(c, b, s2)) -> T(TR(c, r0, s1 ++ s2))

law cat.up.k3:
  for +c: Cx
  for +a: R
  for +b: R
  for +r0: R
  for comp: Comp(c, a, b, r0)
  for +z: U32
  for +s1: String
  for +y1: String
  for +h: U32
  for +w: U32
  for +s2: String
  for +y2: String
  for +e1: {s1 ++ y1 == suf(c, z) : String}
  for +e2: {pos(z, s1) == h : U32}
  for +e3: {s2 ++ y2 == y1 : String}
  for +e4: {pos(h, s2) == w : U32}
  for +ha: T(TR(c, a, s1))
  for +hb: T(TR(c, b, s2))
  T(has(w, E(c, r0, z)))

law tr.Eq2:
  for +c: Cx
  for +r: R
  for +x: String
  for +z: U32
  for +w0: U32
  for +w: U32
  for +y: String
  for +e: {x == y : String}
  for +e2: {w0 == w : U32}
  for +h: T(has(w0, E.go(c, r, "", x, z)))
  T(has(w, E.go(c, r, "", y, z)))

def tr.Eq2(c, r, x, z, w0, w, y, e, e2, h):
  tr.Ep(c, r, y, z, w0, w, e2, tr.Eeq(c, r, x, y, z, w0, e, h))

law cat.pos2:
  for +z: U32
  for +s1: String
  for +s2: String
  for +h: U32
  for +w: U32
  for +e2: {pos(z, s1) == h : U32}
  for +e4: {pos(h, s2) == w : U32}
  {pos(z, s1 ++ s2) == w : U32}

def cat.pos2(z, s1, s2, h, w, e2, e4):
  %pos.app(s1, s2, z) : {_ == w : U32}
  %Equal.sym(U32, pos(z, s1), h, e2) : {pos(_, s2) == w : U32}
  e4

def cat.up.k3(c, a, b, r0, comp, z, s1, y1, h, w, s2, y2, e1, e2, e3, e4, ha, hb):
  tr.Eq2(c, r0, (s1 ++ s2) ++ y2, z, pos(z, s1 ++ s2), w, suf(c, z), app.shift(s1, s2, y2, y1, suf(c, z), e1, e3), cat.pos2(z, s1, s2, h, w, e2, e4), E.intro(c, r0, s1 ++ s2, "", y2, z, comp(s1, s2, ha, hb)))

law cat.up.k2:
  for +c: Cx
  for +a: R
  for +b: R
  for +r0: R
  for comp: Comp(c, a, b, r0)
  for +z: U32
  for +s1: String
  for +y1: String
  for +h: U32
  for +w: U32
  for +e1: {s1 ++ y1 == suf(c, z) : String}
  for +e2: {pos(z, s1) == h : U32}
  for +eh: {suf(c, h) == y1 : String}
  for +ha: T(TR(c, a, s1))
  for k: EW(c, b, "", suf(c, h), h, w)
  T(has(w, E(c, r0, z)))

def cat.up.k2(c, a, b, r0, comp, z, s1, y1, h, w, e1, e2, eh, ha, k):
  match k:
    case (+s2, +y2, +e3, e4, hb):
      cat.up.k3(c, a, b, r0, comp, z, s1, y1, h, w, s2, y2, e1, e2, Equal.trans(String, s2 ++ y2, suf(c, h), y1, e3, eh), e4, ha, hb)

law tr.sufh:
  for +c: Cx
  for +z: U32
  for +s1: String
  for +h: U32
  for +y1: String
  for +e2: {pos(z, s1) == h : U32}
  for +es: {suf(c, pos(z, s1)) == y1 : String}
  {suf(c, h) == y1 : String}

def tr.sufh(c, z, s1, h, y1, e2, es):
  %e2 : {suf(c, _) == y1 : String}
  es

law cat.up.k1:
  for +c: Cx
  for +a: R
  for +b: R
  for +r0: R
  for comp: Comp(c, a, b, r0)
  for +z: U32
  for +h: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hw: T(has(w, E(c, b, h)))
  for k: EW(c, a, "", suf(c, z), z, h)
  T(has(w, E(c, r0, z)))

law cat.up.k0:
  for +c: Cx
  for +a: R
  for +b: R
  for +r0: R
  for comp: Comp(c, a, b, r0)
  for +z: U32
  for +s1: String
  for +y1: String
  for +h: U32
  for +w: U32
  for +e1: {s1 ++ y1 == suf(c, z) : String}
  for +e2: {pos(z, s1) == h : U32}
  for +ha: T(TR(c, a, s1))
  for +hw: T(has(w, E(c, b, h)))
  for ad: Adv(c, z, s1, y1)
  T(has(w, E(c, r0, z)))

def cat.up.k0(c, a, b, r0, comp, z, s1, y1, h, w, e1, e2, ha, hw, ad):
  match ad:
    case (hm, es):
      +eh = tr.sufh(c, z, s1, h, y1, e2, es)
      cat.up.k2(c, a, b, r0, comp, z, s1, y1, h, w, e1, e2, eh, ha, E.elim(c, b, suf(c, h), "", h, w, hw))

def cat.up.k1(c, a, b, r0, comp, z, h, w, ga, hc, hw, k):
  match k:
    case (+s1, +y1, +e1, e2, ha):
      +e3 = e2
      cat.up.k0(c, a, b, r0, comp, z, s1, y1, h, w, e1, e3, ha, hw, adv(c, z, s1, y1, ga, hc, e1))

law cat.up.pt:
  for +c: Cx
  for +a: R
  for +b: R
  for +r0: R
  for comp: Comp(c, a, b, r0)
  for +z: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for u: UW(c, b, E(c, a, z), w)
  T(has(w, E(c, r0, z)))

def cat.up.pt(c, a, b, r0, comp, z, w, ga, hc, u):
  match u:
    case (+h, h1, h2):
      cat.up.k1(c, a, b, r0, comp, z, h, w, ga, hc, h2, E.elim(c, a, suf(c, z), "", z, h, h1))

law cat.up:
  for l: UL
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hl: T(sub(l, U(c, b, E(c, a, z))))
  T(sub(l, E(c, Cat{a, b}, z)))

def cat.up(l, c, a, b, z, ga, hc, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, Cat{a, b}, z), cat.up.pt(c, a, b, Cat{a, b}, +s1 => +s2 => ha => hb => cat.intro(1n+B0(c), cg(c), a, b, s1, s2, "", ha, hb), z, w, ga, hc, U.elim(c, b, E(c, a, z), w, sub.head(w, t, U(c, b, E(c, a, z)), hl))), cat.up(t, c, a, b, z, ga, hc, sub.tail(w, t, U(c, b, E(c, a, z)), hl)))

law cat.same:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(same(U(c, b, E(c, a, z)), E(c, Cat{a, b}, z)))

def cat.same(c, a, b, z, ga, hc):
  same.i(U(c, b, E(c, a, z)), E(c, Cat{a, b}, z), cat.up(U(c, b, E(c, a, z)), c, a, b, z, ga, hc, sub.refl(U(c, b, E(c, a, z)))), cat.down(E(c, Cat{a, b}, z), c, a, b, z, ga, hc, sub.refl(E(c, Cat{a, b}, z))))
# ---- repetition ----

def kept.go(big: Bool, +c: Cx, +kt: U32, +ch: U32) -> Bool:
  match big:
    case True{}:
      True{}
    case False{}:
      U32.is_eq(rdA(c, ((kt + 1 : U32) + ch : U32)), 1)

def kept(+c: Cx, +kt: U32, +x: U32) -> Bool:
  kept.go(U32.is_ge(rdA(c, x), 128), c, kt, rdA(c, x))

def fil(+c: Cx, +kt: U32, l: UL) -> UL:
  match l:
    case UNil{}:
      UNil{}
    case UCon{+x, t}:
      pickc(kept(c, kt, x), x, fil(c, kt, t))

def clos(+c: Cx, +a: R, l: UL, +W: UL) -> Bool:
  match l:
    case UNil{}:
      True{}
    case UCon{+x, t}:
      Bool.and(sub(E(c, a, x), W), clos(c, a, t, W))

def cells(+c: Cx, l: UL) -> Bool:
  match l:
    case UNil{}:
      True{}
    case UCon{+x, t}:
      Bool.and(cell(c, x), cells(c, t))

law tr.cell:
  for +c: Cx
  for +x: U32
  for +h: U32
  for +e: T(U32.is_eq(x, h))
  for +hc: T(cell(c, x))
  T(cell(c, h))

def tr.cell(c, x, h, e, hc):
  %u32.eq.t(x, h, e) : T(cell(c, _))
  hc

law cells.has:
  for +c: Cx
  for +l: UL
  for +x: U32
  for +hl: T(cells(c, l))
  for +h: T(has(x, l))
  T(cell(c, x))

def cells.has(c, l, x, hl, h):
  match l:
    case UNil{}:
      false.elim(T(cell(c, x)), h)
    case UCon{+y, +t}:
      or.c(U32.is_eq(y, x), has(x, t), T(cell(c, x)), h, +e => tr.cell(c, y, x, e, and.l(cell(c, y), cells(c, t), hl)), +h2 => cells.has(c, t, x, and.r(cell(c, y), cells(c, t), hl), h2))

law cells.sub:
  for l: UL
  for +c: Cx
  for +m: UL
  for +hs: T(sub(l, m))
  for +hm: T(cells(c, m))
  T(cells(c, l))

def cells.sub(l, c, m, hs, hm):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      and.i(cell(c, x), cells(c, t), cells.has(c, m, x, hm, sub.head(x, t, m, hs)), cells.sub(t, c, m, sub.tail(x, t, m, hs), hm))

law cells.uapp:
  for a: UL
  for +c: Cx
  for +b: UL
  for +h1: T(cells(c, a))
  for +h2: T(cells(c, b))
  T(cells(c, uapp(a, b)))

def cells.uapp(a, c, b, h1, h2):
  match a:
    case UNil{}:
      h2
    case UCon{+x, +t}:
      and.i(cell(c, x), cells(c, uapp(t, b)), and.l(cell(c, x), cells(c, t), h1), cells.uapp(t, c, b, and.r(cell(c, x), cells(c, t), h1), h2))

def pr.fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def pr.snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

law adv.c:
  for +c: Cx
  for +z: U32
  for +q: String
  for +y: String
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +e: {q ++ y == suf(c, z) : String}
  T(cell(c, pos(z, q)))

def adv.c(c, z, q, y, ga, hc, e):
  pr.fst(T(cell(c, pos(z, q))), {suf(c, pos(z, q)) == y : String}, adv(c, z, q, y, ga, hc, e))

law adv.s:
  for +c: Cx
  for +z: U32
  for +q: String
  for +y: String
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +e: {q ++ y == suf(c, z) : String}
  {suf(c, pos(z, q)) == y : String}

def adv.s(c, z, q, y, ga, hc, e):
  pr.snd(T(cell(c, pos(z, q))), {suf(c, pos(z, q)) == y : String}, adv(c, z, q, y, ga, hc, e))

law E.cell.k:
  for +c: Cx
  for +r: R
  for +z: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for h: EW(c, r, "", suf(c, z), z, w)
  T(cell(c, w))

law tr.cell2:
  for +c: Cx
  for +x: U32
  for +h: U32
  for +e: {x == h : U32}
  for +hc: T(cell(c, x))
  T(cell(c, h))

def tr.cell2(c, x, h, e, hc):
  %e : T(cell(c, _))
  hc

def E.cell.k(c, r, z, w, ga, hc, h):
  match h:
    case (+q, +y, +e1, e2, ht):
      tr.cell2(c, pos(z, q), w, e2, adv.c(c, z, q, y, ga, hc, e1))

law E.cell:
  for +c: Cx
  for +r: R
  for +z: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +h: T(has(w, E(c, r, z)))
  T(cell(c, w))

def E.cell(c, r, z, w, ga, hc, h):
  E.cell.k(c, r, z, w, ga, hc, E.elim(c, r, suf(c, z), "", z, w, h))

law cells.of:
  for l: UL
  for +c: Cx
  for +r: R
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hl: T(sub(l, E(c, r, z)))
  T(cells(c, l))

def cells.of(l, c, r, z, ga, hc, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      and.i(cell(c, x), cells(c, t), E.cell(c, r, z, x, ga, hc, sub.head(x, t, E(c, r, z), hl)), cells.of(t, c, r, z, ga, hc, sub.tail(x, t, E(c, r, z), hl)))

law E.cells:
  for +c: Cx
  for +r: R
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(cells(c, E(c, r, z)))

def E.cells(c, r, z, ga, hc):
  cells.of(E(c, r, z), c, r, z, ga, hc, sub.refl(E(c, r, z)))

law tr.Ex:
  for +c: Cx
  for +a: R
  for +x: U32
  for +h: U32
  for +W: UL
  for +e: T(U32.is_eq(x, h))
  for +hs: T(sub(E(c, a, x), W))
  T(sub(E(c, a, h), W))

def tr.Ex(c, a, x, h, W, e, hs):
  %u32.eq.t(x, h, e) : T(sub(E(c, a, _), W))
  hs

law clos.has:
  for +c: Cx
  for +a: R
  for +l: UL
  for +W: UL
  for +x: U32
  for +hc: T(clos(c, a, l, W))
  for +h: T(has(x, l))
  T(sub(E(c, a, x), W))

def clos.has(c, a, l, W, x, hc, h):
  match l:
    case UNil{}:
      false.elim(T(sub(E(c, a, x), W)), h)
    case UCon{+y, +t}:
      or.c(U32.is_eq(y, x), has(x, t), T(sub(E(c, a, x), W)), h, +e => tr.Ex(c, a, y, x, W, e, and.l(sub(E(c, a, y), W), clos(c, a, t, W), hc)), +h2 => clos.has(c, a, t, W, x, and.r(sub(E(c, a, y), W), clos(c, a, t, W), hc), h2))

law clos.weak:
  for l: UL
  for +c: Cx
  for +a: R
  for +W: UL
  for +W2: UL
  for +hc: T(clos(c, a, l, W))
  for +hs: T(sub(W, W2))
  T(clos(c, a, l, W2))

def clos.weak(l, c, a, W, W2, hc, hs):
  match l:
    case UNil{}:
      {==}
    case UCon{+y, +t}:
      and.i(sub(E(c, a, y), W2), clos(c, a, t, W2), sub.trans(E(c, a, y), W, W2, and.l(sub(E(c, a, y), W), clos(c, a, t, W), hc), hs), clos.weak(t, c, a, W, W2, and.r(sub(E(c, a, y), W), clos(c, a, t, W), hc), hs))

# filtering

law fil.in:
  for l: UL
  for +c: Cx
  for +kt: U32
  for +x: U32
  for +hk: T(kept(c, kt, x))
  for +h: T(has(x, l))
  T(has(x, fil(c, kt, l)))

law pick.in2:
  for b: Bool
  for +i: U32
  for +l: UL
  for +z: U32
  for +he: T(U32.is_eq(i, z))
  for +hb: T(b)
  T(has(z, pickc(b, i, l)))

def pick.in2(b, i, l, z, he, hb):
  match b:
    case True{}:
      has.head(z, i, l, he)
    case False{}:
      false.elim(T(has(z, l)), hb)

law tr.kept:
  for +c: Cx
  for +kt: U32
  for +x: U32
  for +h: U32
  for +e: T(U32.is_eq(h, x))
  for +hk: T(kept(c, kt, x))
  T(kept(c, kt, h))

def tr.kept(c, kt, x, h, e, hk):
  %u32.eq.t(x, h, u32.eq.sym(h, x, e)) : T(kept(c, kt, _))
  hk

def fil.in(l, c, kt, x, hk, h):
  match l:
    case UNil{}:
      false.elim(T(has(x, UNil{})), h)
    case UCon{+y, +t}:
      or.c(U32.is_eq(y, x), has(x, t), T(has(x, pickc(kept(c, kt, y), y, fil(c, kt, t)))), h, +e => pick.in2(kept(c, kt, y), y, fil(c, kt, t), x, e, tr.kept(c, kt, x, y, e, hk)), +h2 => pickc.tail(kept(c, kt, y), y, fil(c, kt, t), x, fil.in(t, c, kt, x, hk, h2)))

law fil.has:
  for l: UL
  for +c: Cx
  for +kt: U32
  for +x: U32
  for +h: T(has(x, fil(c, kt, l)))
  T(has(x, l))

def fil.has(l, c, kt, x, h):
  match l:
    case UNil{}:
      h
    case UCon{+y, +t}:
      pickc.c(kept(c, kt, y), y, fil(c, kt, t), x, T(has(x, UCon{y, t})), h, hb => +e => has.head(x, y, t, e), +h2 => has.tail(x, y, t, fil.has(t, c, kt, x, h2)))

law fil.kept:
  for l: UL
  for +c: Cx
  for +kt: U32
  for +x: U32
  for +h: T(has(x, fil(c, kt, l)))
  T(kept(c, kt, x))

def fil.kept(l, c, kt, x, h):
  match l:
    case UNil{}:
      false.elim(T(kept(c, kt, x)), h)
    case UCon{+y, +t}:
      pickc.c(kept(c, kt, y), y, fil(c, kt, t), x, T(kept(c, kt, x)), h, +hb => +e => tr.kept(c, kt, y, x, u32.eq.sym(y, x, e), hb), +h2 => fil.kept(t, c, kt, x, h2))

law fil.sub:
  for l: UL
  for +c: Cx
  for +kt: U32
  for +a: UL
  for +b: UL
  for +hl: T(sub(l, fil(c, kt, a)))
  for +hs: T(sub(a, b))
  T(sub(l, fil(c, kt, b)))

def fil.sub(l, c, kt, a, b, hl, hs):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      sub.cons(x, t, fil(c, kt, b), fil.in(b, c, kt, x, fil.kept(a, c, kt, x, sub.head(x, t, fil(c, kt, a), hl)), sub.has(x, a, b, hs, fil.has(a, c, kt, x, sub.head(x, t, fil(c, kt, a), hl)))), fil.sub(t, c, kt, a, b, sub.tail(x, t, fil(c, kt, a), hl), hs))

law pickc.mono:
  for b: Bool
  for +x: U32
  for +l: UL
  for +m: UL
  for +h: T(sub(l, m))
  T(sub(pickc(b, x, l), pickc(b, x, m)))

def pickc.mono(b, x, l, m, h):
  match b:
    case True{}:
      sub.cons(x, l, UCon{x, m}, has.self(x, m), sub.weak(l, x, m, h))
    case False{}:
      h

# what repetition means

law star.one:
  for +c: Cx
  for +a: R
  for +s: String
  for +h: T(TR(c, a, s))
  T(TR(c, Star{a}, s))

def star.one(c, a, s, h):
  tr.tr(c, Star{a}, s ++ "", s, app.nil(s), star.intro(1n, 1n+B0(c), cg(c), a, s ++ "", seq2.intro(1n+B0(c), cg(c), a, Emp{}, s, "", h, {==})))

law star.snoc:
  for +m: Nat
  for +c: Cx
  for +a: R
  for +s1: String
  for +s2: String
  for +hq: T(sem(1n+B0(c), cg(c), exact(m, a), s1, ""))
  for +ha: T(TR(c, a, s2))
  T(TR(c, Star{a}, s1 ++ s2))

law tr.str:
  for +c: Cx
  for +a: R
  for +x1: String
  for +x2: String
  for +s2: String
  for +s1: String
  for +e: {x1 ++ x2 == s1 : String}
  for +h: T(TR(c, Star{a}, x1 ++ (x2 ++ s2)))
  T(TR(c, Star{a}, s1 ++ s2))

def tr.str(c, a, x1, x2, s2, s1, e, h):
  %e : T(TR(c, Star{a}, _ ++ s2))
  tr.tr(c, Star{a}, x1 ++ (x2 ++ s2), (x1 ++ x2) ++ s2, app.assoc.sym(x1, x2, s2), h)

law star.zero:
  for +c: Cx
  for +a: R
  for +s1: String
  for +s2: String
  for +e: {s1 == "" : String}
  for +ha: T(TR(c, a, s2))
  T(TR(c, Star{a}, s1 ++ s2))

def star.zero(c, a, s1, s2, e, ha):
  %Equal.sym(String, s1, "", e) : T(TR(c, Star{a}, _ ++ s2))
  star.one(c, a, s2, ha)

def star.snoc(m, c, a, s1, s2, hq, ha):
  match m:
    case 0n:
      star.zero(c, a, s1, s2, emp.nil(1n+B0(c), cg(c), s1, hq), ha)
    case 1n+j:
      seq2.with(1n+B0(c), cg(c), a, exact(j, a), s1, seq2.elim(1n+B0(c), cg(c), a, exact(j, a), s1, hq), T(TR(c, Star{a}, s1 ++ s2)), +x1 => +x2 => +e => +h1 => +h2 => tr.str(c, a, x1, x2, s2, s1, e, star.cons(1n+B0(c), cg(c), a, x1, x2 ++ s2, h1, star.snoc(j, c, a, x2, s2, h2, ha))))

law star.app.k:
  for +c: Cx
  for +a: R
  for +s1: String
  for +s2: String
  for w: ExW(1n+B0(c), cg(c), a, s1)
  for +ha: T(TR(c, a, s2))
  T(TR(c, Star{a}, s1 ++ s2))

def star.app.k(c, a, s1, s2, w, ha):
  match w:
    case (+m, hm):
      star.snoc(m, c, a, s1, s2, hm, ha)

law star.app:
  for +c: Cx
  for +a: R
  for +s1: String
  for +s2: String
  for +h1: T(TR(c, Star{a}, s1))
  for +h2: T(TR(c, a, s2))
  T(TR(c, Star{a}, s1 ++ s2))

def star.app(c, a, s1, s2, h1, h2):
  star.app.k(c, a, s1, s2, star.elim(1n+B0(c), cg(c), a, s1, "", h1), h2)

law star.close:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +x: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hi: T(cell(c, i0))
  for +hx: T(has(x, E(c, Star{a}, i0)))
  for +hw: T(has(w, E(c, a, x)))
  T(has(w, E(c, Star{a}, i0)))

def star.close(c, a, i0, x, w, ga, hi, hx, hw):
  cat.up.pt(c, Star{a}, a, Star{a}, +s1 => +s2 => +h1 => +h2 => star.app(c, a, s1, s2, h1, h2), i0, w, ga, hi, (x, hx, hw))

law star.close.l:
  for l: UL
  for +c: Cx
  for +a: R
  for +i0: U32
  for +x: U32
  for +ga: T(Glob(c))
  for +hi: T(cell(c, i0))
  for +hx: T(has(x, E(c, Star{a}, i0)))
  for +hl: T(sub(l, E(c, a, x)))
  T(sub(l, E(c, Star{a}, i0)))

def star.close.l(l, c, a, i0, x, ga, hi, hx, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, Star{a}, i0), star.close(c, a, i0, x, w, ga, hi, hx, sub.head(w, t, E(c, a, x), hl)), star.close.l(t, c, a, i0, x, ga, hi, hx, sub.tail(w, t, E(c, a, x), hl)))

def Inv(+c: Cx, +a: R, +i0: U32, +kt: U32, +V: UL, +L: UL, +acc: UL) -> Bool:
  Bool.and(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))))

law inv.p1:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(sub(uapp(V, L), E(c, Star{a}, i0)))

def inv.p1(c, a, i0, kt, V, L, acc, h):
  and.l(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h)

law inv.p2:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(has(i0, uapp(V, L)))

def inv.p2(c, a, i0, kt, V, L, acc, h):
  and.l(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), and.r(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h))

law inv.p3:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(clos(c, a, V, uapp(V, L)))

def inv.p3(c, a, i0, kt, V, L, acc, h):
  and.l(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))), and.r(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), and.r(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h)))

law inv.p4:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(cells(c, uapp(V, L)))

def inv.p4(c, a, i0, kt, V, L, acc, h):
  and.l(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)), and.r(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))), and.r(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), and.r(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h))))

law inv.p5:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(sub(acc, fil(c, kt, V)))

def inv.p5(c, a, i0, kt, V, L, acc, h):
  and.l(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc), and.r(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)), and.r(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))), and.r(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), and.r(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h)))))

law inv.p6:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h: T(Inv(c, a, i0, kt, V, L, acc))
  T(sub(fil(c, kt, V), acc))

def inv.p6(c, a, i0, kt, V, L, acc, h):
  and.r(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc), and.r(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)), and.r(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))), and.r(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), and.r(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h)))))

law inv.i:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for +acc: UL
  for +h1: T(sub(uapp(V, L), E(c, Star{a}, i0)))
  for +h2: T(has(i0, uapp(V, L)))
  for +h3: T(clos(c, a, V, uapp(V, L)))
  for +h4: T(cells(c, uapp(V, L)))
  for +h5: T(sub(acc, fil(c, kt, V)))
  for +h6: T(sub(fil(c, kt, V), acc))
  T(Inv(c, a, i0, kt, V, L, acc))

def inv.i(c, a, i0, kt, V, L, acc, h1, h2, h3, h4, h5, h6):
  and.i(sub(uapp(V, L), E(c, Star{a}, i0)), Bool.and(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))))), h1, and.i(has(i0, uapp(V, L)), Bool.and(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)))), h2, and.i(clos(c, a, V, uapp(V, L)), Bool.and(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc))), h3, and.i(cells(c, uapp(V, L)), Bool.and(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc)), h4, and.i(sub(acc, fil(c, kt, V)), sub(fil(c, kt, V), acc), h5, h6)))))

law inv.init:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +hc: T(cell(c, i0))
  T(Inv(c, a, i0, kt, UNil{}, UCon{i0, UNil{}}, UNil{}))

def inv.init(c, a, i0, kt, hc):
  inv.i(c, a, i0, kt, UNil{}, UCon{i0, UNil{}}, UNil{}, sub.cons(i0, UNil{}, E(c, Star{a}, i0), E.intro.here(c, Star{a}, "", suf(c, i0), i0, {==}), {==}), has.self(i0, UNil{}), {==}, and.i(cell(c, i0), True{}, hc, {==}), {==}, {==})

law inv.step:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +x: U32
  for +t: UL
  for +L2: UL
  for +acc: UL
  for +ga: T(Glob(c))
  for +h: T(Inv(c, a, i0, kt, V, UCon{x, t}, acc))
  for +h1: T(sub(E(c, a, x), UCon{x, uapp(V, L2)}))
  for +h2: T(sub(L2, uapp(t, E(c, a, x))))
  for +h3: T(sub(t, L2))
  T(Inv(c, a, i0, kt, UCon{x, V}, L2, pickc(kept(c, kt, x), x, acc)))

def inv.step(c, a, i0, kt, V, x, t, L2, acc, ga, h, h1, h2, h3):
  +a1 = inv.p1(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +a2 = inv.p2(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +a3 = inv.p3(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +a4 = inv.p4(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +a5 = inv.p5(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +a6 = inv.p6(c, a, i0, kt, V, UCon{x, t}, acc, h)
  +hxW = uapp.in.r(x, V, UCon{x, t}, has.self(x, t))
  +hxR = sub.has(x, uapp(V, UCon{x, t}), E(c, Star{a}, i0), a1, hxW)
  +sVW = sub.uapp.l(V, V, UCon{x, t}, sub.refl(V))
  +stW = sub.uapp.r(t, V, UCon{x, t}, sub.weak(t, x, t, sub.refl(t)))
  +sVN = sub.weak(V, x, uapp(V, L2), sub.uapp.l(V, V, L2, sub.refl(V)))
  +sWW = uapp.sub(V, UCon{x, t}, UCon{x, uapp(V, L2)}, sVN, sub.cons(x, t, UCon{x, uapp(V, L2)}, has.self(x, uapp(V, L2)), sub.weak(t, x, uapp(V, L2), sub.uapp.r(t, V, L2, h3))))
  +sVR = sub.trans(V, uapp(V, UCon{x, t}), E(c, Star{a}, i0), sVW, a1)
  +stR = sub.trans(t, uapp(V, UCon{x, t}), E(c, Star{a}, i0), stW, a1)
  +hi = cells.has(c, uapp(V, UCon{x, t}), i0, a4, a2)
  +sER = star.close.l(E(c, a, x), c, a, i0, x, ga, hi, hxR, sub.refl(E(c, a, x)))
  +sLR = sub.trans(L2, uapp(t, E(c, a, x)), E(c, Star{a}, i0), h2, uapp.sub(t, E(c, a, x), E(c, Star{a}, i0), stR, sER))
  +cx = cells.has(c, uapp(V, UCon{x, t}), x, a4, hxW)
  +cV = cells.sub(V, c, uapp(V, UCon{x, t}), sVW, a4)
  +ct = cells.sub(t, c, uapp(V, UCon{x, t}), stW, a4)
  +cL = cells.sub(L2, c, uapp(t, E(c, a, x)), h2, cells.uapp(t, c, E(c, a, x), ct, E.cells(c, a, x, ga, cx)))
  inv.i(c, a, i0, kt, UCon{x, V}, L2, pickc(kept(c, kt, x), x, acc), sub.cons(x, uapp(V, L2), E(c, Star{a}, i0), hxR, uapp.sub(V, L2, E(c, Star{a}, i0), sVR, sLR)), sub.has(i0, uapp(V, UCon{x, t}), UCon{x, uapp(V, L2)}, sWW, a2), and.i(sub(E(c, a, x), UCon{x, uapp(V, L2)}), clos(c, a, V, UCon{x, uapp(V, L2)}), h1, clos.weak(V, c, a, uapp(V, UCon{x, t}), UCon{x, uapp(V, L2)}, a3, sWW)), and.i(cell(c, x), cells(c, uapp(V, L2)), cx, cells.uapp(V, c, L2, cV, cL)), pickc.mono(kept(c, kt, x), x, acc, fil(c, kt, V), a5), pickc.mono(kept(c, kt, x), x, fil(c, kt, V), acc, a6))

law in.unil:
  for +z: U32
  for +V: UL
  for +h: T(has(z, uapp(V, UNil{})))
  T(has(z, V))

def in.unil(z, V, h):
  or.c(has(z, V), has(z, UNil{}), T(has(z, V)), uapp.or(z, V, UNil{}, h), h1 => h1, hn => false.elim(T(has(z, V)), hn))

law tr.hasp:
  for +w0: U32
  for +w: U32
  for +V: UL
  for +e: {w0 == w : U32}
  for +h: T(has(w0, V))
  T(has(w, V))

def tr.hasp(w0, w, V, e, h):
  %e : T(has(_, V))
  h

law star.clo:
  for +m: Nat
  for +c: Cx
  for +a: R
  for +V: UL
  for +q: String
  for +y: String
  for +x: U32
  for +ga: T(Glob(c))
  for +hV: T(clos(c, a, V, uapp(V, UNil{})))
  for +hVc: T(cells(c, V))
  for +hx: T(has(x, V))
  for +es: {q ++ y == suf(c, x) : String}
  for +hq: T(sem(1n+B0(c), cg(c), exact(m, a), q, ""))
  T(has(pos(x, q), V))

law tr.nil.has:
  for +x: U32
  for +q: String
  for +V: UL
  for +e: {q == "" : String}
  for +h: T(has(x, V))
  T(has(pos(x, q), V))

def tr.nil.has(x, q, V, e, h):
  %Equal.sym(String, q, "", e) : T(has(pos(x, _), V))
  h

def star.clo(m, c, a, V, q, y, x, ga, hV, hVc, hx, es, hq):
  match m:
    case 0n:
      tr.nil.has(x, q, V, emp.nil(1n+B0(c), cg(c), q, hq), hx)
    case 1n+j:
      seq2.with(1n+B0(c), cg(c), a, exact(j, a), q, seq2.elim(1n+B0(c), cg(c), a, exact(j, a), q, hq), T(has(pos(x, q), V)), +s1 => +s2 => +e3 => +h1 => +h2 => tr.hasp(pos(pos(x, s1), s2), pos(x, q), V, pos.cat(x, s1, s2, q, pos(x, q), e3, {==}), star.clo(j, c, a, V, s2, y, pos(x, s1), ga, hV, hVc, in.unil(pos(x, s1), V, sub.has(pos(x, s1), E(c, a, x), uapp(V, UNil{}), clos.has(c, a, V, uapp(V, UNil{}), x, hV, hx), tr.Eeq(c, a, s1 ++ (s2 ++ y), suf(c, x), x, pos(x, s1), cat.e4(s1, s2, y, q, suf(c, x), e3, es), E.intro(c, a, s1, "", s2 ++ y, x, h1)))), Equal.sym(String, suf(c, pos(x, s1)), s2 ++ y, adv.s(c, x, s1, s2 ++ y, ga, cells.has(c, V, x, hVc, hx), cat.e4(s1, s2, y, q, suf(c, x), e3, es))), h2)))

law star.pt.k2:
  for +m: Nat
  for +c: Cx
  for +a: R
  for +V: UL
  for +i0: U32
  for +q: String
  for +y: String
  for +w: U32
  for +ga: T(Glob(c))
  for +hV: T(clos(c, a, V, uapp(V, UNil{})))
  for +hVc: T(cells(c, V))
  for +hi: T(has(i0, V))
  for +e1: {q ++ y == suf(c, i0) : String}
  for +e2: {pos(i0, q) == w : U32}
  for +hm: T(sem(1n+B0(c), cg(c), exact(m, a), q, ""))
  T(has(w, V))

def star.pt.k2(m, c, a, V, i0, q, y, w, ga, hV, hVc, hi, e1, e2, hm):
  tr.hasp(pos(i0, q), w, V, e2, star.clo(m, c, a, V, q, y, i0, ga, hV, hVc, hi, e1, hm))

law star.pt.k1:
  for +c: Cx
  for +a: R
  for +V: UL
  for +i0: U32
  for +q: String
  for +y: String
  for +w: U32
  for +ga: T(Glob(c))
  for +hV: T(clos(c, a, V, uapp(V, UNil{})))
  for +hVc: T(cells(c, V))
  for +hi: T(has(i0, V))
  for +e1: {q ++ y == suf(c, i0) : String}
  for +e2: {pos(i0, q) == w : U32}
  for k: ExW(1n+B0(c), cg(c), a, q)
  T(has(w, V))

def star.pt.k1(c, a, V, i0, q, y, w, ga, hV, hVc, hi, e1, e2, k):
  match k:
    case (+m, hm):
      star.pt.k2(m, c, a, V, i0, q, y, w, ga, hV, hVc, hi, e1, e2, hm)

law star.pt:
  for +c: Cx
  for +a: R
  for +V: UL
  for +i0: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hV: T(clos(c, a, V, uapp(V, UNil{})))
  for +hVc: T(cells(c, V))
  for +hi: T(has(i0, V))
  for k: EW(c, Star{a}, "", suf(c, i0), i0, w)
  T(has(w, V))

def star.pt(c, a, V, i0, w, ga, hV, hVc, hi, k):
  match k:
    case (+q, +y, +e1, e2, ht):
      star.pt.k1(c, a, V, i0, q, y, w, ga, hV, hVc, hi, e1, e2, star.elim(1n+B0(c), cg(c), a, q, "", ht))

law star.down:
  for l: UL
  for +c: Cx
  for +a: R
  for +V: UL
  for +i0: U32
  for +ga: T(Glob(c))
  for +hV: T(clos(c, a, V, uapp(V, UNil{})))
  for +hVc: T(cells(c, V))
  for +hi: T(has(i0, V))
  for +hl: T(sub(l, E(c, Star{a}, i0)))
  T(sub(l, V))

def star.down(l, c, a, V, i0, ga, hV, hVc, hi, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, V, star.pt(c, a, V, i0, w, ga, hV, hVc, hi, E.elim(c, Star{a}, suf(c, i0), "", i0, w, sub.head(w, t, E(c, Star{a}, i0), hl))), star.down(t, c, a, V, i0, ga, hV, hVc, hi, sub.tail(w, t, E(c, Star{a}, i0), hl)))

law inv.fin:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +acc: UL
  for +ga: T(Glob(c))
  for +h: T(Inv(c, a, i0, kt, V, UNil{}, acc))
  T(same(acc, fil(c, kt, E(c, Star{a}, i0))))

def inv.fin(c, a, i0, kt, V, acc, ga, h):
  +a1 = inv.p1(c, a, i0, kt, V, UNil{}, acc, h)
  +a2 = inv.p2(c, a, i0, kt, V, UNil{}, acc, h)
  +a3 = inv.p3(c, a, i0, kt, V, UNil{}, acc, h)
  +a4 = inv.p4(c, a, i0, kt, V, UNil{}, acc, h)
  +a5 = inv.p5(c, a, i0, kt, V, UNil{}, acc, h)
  +a6 = inv.p6(c, a, i0, kt, V, UNil{}, acc, h)
  +sVW = sub.uapp.l(V, V, UNil{}, sub.refl(V))
  +hiV = in.unil(i0, V, a2)
  +cV = cells.sub(V, c, uapp(V, UNil{}), sVW, a4)
  +sVR = sub.trans(V, uapp(V, UNil{}), E(c, Star{a}, i0), sVW, a1)
  +sRV = star.down(E(c, Star{a}, i0), c, a, V, i0, ga, a3, cV, hiV, sub.refl(E(c, Star{a}, i0)))
  same.i(acc, fil(c, kt, E(c, Star{a}, i0)), sub.trans(acc, fil(c, kt, V), fil(c, kt, E(c, Star{a}, i0)), a5, fil.sub(fil(c, kt, V), c, kt, V, E(c, Star{a}, i0), sub.refl(fil(c, kt, V)), sVR)), sub.trans(fil(c, kt, E(c, Star{a}, i0)), fil(c, kt, V), acc, fil.sub(fil(c, kt, E(c, Star{a}, i0)), c, kt, E(c, Star{a}, i0), V, sub.refl(fil(c, kt, E(c, Star{a}, i0))), sRV), a6))

# drop

law drop.k.sub:
  for b: Bool
  for +h: U32
  for +r: UL
  for +c: UL
  for +hh: T(has(h, c))
  for +hr: T(sub(r, c))
  T(sub(drop.k(b, h, r), c))

def drop.k.sub(b, h, r, c, hh, hr):
  match b:
    case True{}:
      hr
    case False{}:
      sub.cons(h, r, c, hh, hr)

law drop.sub:
  for +e: U32
  for l: UL
  for +c: UL
  for +h: T(sub(l, c))
  T(sub(drop(e, l), c))

def drop.sub(e, l, c, h):
  match l:
    case UNil{}:
      {==}
    case UCon{+x, +t}:
      drop.k.sub(U32.is_eq(x, e), x, drop(e, t), c, sub.head(x, t, c, h), drop.sub(e, t, c, sub.tail(x, t, c, h)))

law drop.k.in:
  for b: Bool
  for +h: U32
  for +r: UL
  for +z: U32
  for +hr: T(has(z, r))
  T(has(z, drop.k(b, h, r)))

def drop.k.in(b, h, r, z, hr):
  match b:
    case True{}:
      hr
    case False{}:
      has.tail(z, h, r, hr)

law drop.k.head:
  for b: Bool
  for +h: U32
  for +r: UL
  for +z: U32
  for +e: {b == False{} : Bool}
  for +he: T(U32.is_eq(h, z))
  T(has(z, drop.k(b, h, r)))

def drop.k.head(b, h, r, z, e, he):
  match b:
    case True{}:
      absurd(T(has(z, drop.k(True{}, h, r))), true.not_false(e))
    case False{}:
      has.head(z, h, r, he)

law ne.tr:
  for +h: U32
  for +z: U32
  for +e: U32
  for +hn: {U32.is_eq(z, e) == False{} : Bool}
  for +he: T(U32.is_eq(h, z))
  {U32.is_eq(h, e) == False{} : Bool}

def ne.tr(h, z, e, hn, he):
  %u32.eq.t(z, h, u32.eq.sym(h, z, he)) : {U32.is_eq(_, e) == False{} : Bool}
  hn

law drop.in:
  for +e: U32
  for +l: UL
  for +z: U32
  for +hn: {U32.is_eq(z, e) == False{} : Bool}
  for +h: T(has(z, l))
  T(has(z, drop(e, l)))

def drop.in(e, l, z, hn, h):
  match l:
    case UNil{}:
      false.elim(T(has(z, drop(e, UNil{}))), h)
    case UCon{+x, +t}:
      or.c(U32.is_eq(x, z), has(z, t), T(has(z, drop.k(U32.is_eq(x, e), x, drop(e, t)))), h, +he => drop.k.head(U32.is_eq(x, e), x, drop(e, t), z, ne.tr(x, z, e, hn, he), he), +h2 => drop.k.in(U32.is_eq(x, e), x, drop(e, t), z, drop.in(e, t, z, hn, h2)))

law star.h1:
  for l: UL
  for +x: U32
  for +r: UL
  for +V: UL
  for +t: UL
  for +hl: T(sub(l, r))
  T(sub(l, UCon{x, uapp(V, merge(t, drop(x, r)))}))

def star.h1(l, x, r, V, t, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t2}:
      sub.cons(w, t2, UCon{x, uapp(V, merge(t, drop(x, r)))}, bool.split(U32.is_eq(w, x), T(has(w, UCon{x, uapp(V, merge(t, drop(x, r)))})), +e => has.head(w, x, uapp(V, merge(t, drop(x, r))), u32.eq.sym(w, x, e)), +ne => has.tail(w, x, uapp(V, merge(t, drop(x, r))), uapp.in.r(w, V, merge(t, drop(x, r)), merge.in.r(w, t, drop(x, r), drop.in(x, r, w, ne, sub.head(w, t2, r, hl)))))), star.h1(t2, x, r, V, t, sub.tail(w, t2, r, hl)))

law inv.star:
  for +c: Cx
  for +a: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +x: U32
  for +t: UL
  for +r: UL
  for +acc: UL
  for +ga: T(Glob(c))
  for +h: T(Inv(c, a, i0, kt, V, UCon{x, t}, acc))
  for +hr: T(same(r, E(c, a, x)))
  T(Inv(c, a, i0, kt, UCon{x, V}, merge(t, drop(x, r)), pickc(kept(c, kt, x), x, acc)))

def inv.star(c, a, i0, kt, V, x, t, r, acc, ga, h, hr):
  inv.step(c, a, i0, kt, V, x, t, merge(t, drop(x, r)), acc, ga, h, star.h1(E(c, a, x), x, r, V, t, same.r(r, E(c, a, x), hr)), merge.sub(t, drop(x, r), uapp(t, E(c, a, x)), sub.uapp.l(t, t, E(c, a, x), sub.refl(t)), drop.sub(x, r, uapp(t, E(c, a, x)), sub.uapp.r(r, t, E(c, a, x), same.l(r, E(c, a, x), hr)))), sub.merge.l(t, t, drop(x, r), sub.refl(t)))
# ---- single characters ----

law at.suf.k:
  for +c: Cx
  for +z: U32
  for +ga: T(Glob(c))
  for w: CellW(c, z)
  T(at(c, suf(c, z), z))

def at.suf.k(c, z, ga, w):
  match w:
    case (+u, +e1, e2):
      %e2 : T(at(c, suf(c, z), _))
      at.pos(c, u, suf(c, z), cnx(c), cell.rec.at(c, u, suf(c, z), ga, e1))

law at.suf:
  for +c: Cx
  for +z: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(at(c, suf(c, z), z))

def at.suf(c, z, ga, hc):
  at.suf.k(c, z, ga, cell.elim(c, z, hc))

def lf(+r: R, p: String) -> Bool:
  match p:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      match t:
        case SNil{}:
          cmatch(r, code(h))
        case SCon{h2, t2}:
          False{}

law leaf.alt:
  for +a: R
  for +b: R
  for p: String
  {orelse(lf(a, p), u => lf(b, p)) == lf(Alt{a, b}, p) : Bool}

def leaf.alt(a, b, p):
  match p:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match t:
        case SNil{}:
          or.eq(cmatch(a, code(h)), cmatch(b, code(h)))
        case SCon{h2, t2}:
          {==}

law leaf.tr:
  for +c: Cx
  for +r: R
  for +p: String
  for +hl: T(leafy(r))
  {TR(c, r, p) == lf(r, p) : Bool}

def leaf.tr(c, r, p, hl):
  match r:
    case Lit{+x}:
      match x:
        case Chr{+a}:
          match p:
            case SNil{}:
              {==}
            case SCon{+h, +t}:
              match h:
                case Chr{+b}:
                  match t:
                    case SNil{}:
                      {==}
                    case SCon{h2, t2}:
                      {==}
    case Rng{+lo, +hi}:
      match p:
        case SNil{}:
          {==}
        case SCon{+h, +t}:
          match t:
            case SNil{}:
              {==}
            case SCon{h2, t2}:
              {==}
    case Alt{+a, +b}:
      %Equal.sym(Bool, TR(c, a, p), lf(a, p), leaf.tr(c, a, p, and.l(leafy(a), leafy(b), hl))) : {orelse(_, u => TR(c, b, p)) == lf(Alt{a, b}, p) : Bool}
      %Equal.sym(Bool, TR(c, b, p), lf(b, p), leaf.tr(c, b, p, and.r(leafy(a), leafy(b), hl))) : {orelse(lf(a, p), u => _) == lf(Alt{a, b}, p) : Bool}
      leaf.alt(a, b, p)
    case Emp{}:
      false.elim({TR(c, Emp{}, p) == lf(Emp{}, p) : Bool}, hl)
    case Bad{}:
      false.elim({TR(c, Bad{}, p) == lf(Bad{}, p) : Bool}, hl)
    case Cat{a, b}:
      false.elim({TR(c, Cat{a, b}, p) == lf(Cat{a, b}, p) : Bool}, hl)
    case Star{a}:
      false.elim({TR(c, Star{a}, p) == lf(Star{a}, p) : Bool}, hl)
    case Ref{n}:
      false.elim({TR(c, Ref{n}, p) == lf(Ref{n}, p) : Bool}, hl)

law E.z2:
  for +c: Cx
  for +r: R
  for x: String
  for +h1: Char
  for +h2: Char
  for +t: String
  for +i: U32
  for +hl: T(leafy(r))
  {E.go(c, r, SCon{h1, SCon{h2, t}}, x, i) == UNil{} : UL}

def E.z2(c, r, x, h1, h2, t, i, hl):
  match x:
    case SNil{}:
      %Equal.sym(Bool, TR(c, r, SCon{h1, SCon{h2, t}}), False{}, leaf.tr(c, r, SCon{h1, SCon{h2, t}}, hl)) : {pickc(_, i, UNil{}) == UNil{} : UL}
      {==}
    case SCon{+a, +t2}:
      %Equal.sym(Bool, TR(c, r, SCon{h1, SCon{h2, t}}), False{}, leaf.tr(c, r, SCon{h1, SCon{h2, t}}, hl)) : {pickc(_, i, E.go(c, r, SCon{h1, SCon{h2, t}} ++ SCon{a, SNil{}}, t2, (i + 1 : U32))) == UNil{} : UL}
      E.z2(c, r, t2, h1, h2, t ++ SCon{a, SNil{}}, (i + 1 : U32), hl)

law E.leaf.nil:
  for +c: Cx
  for +r: R
  for +z: U32
  for +hl: T(leafy(r))
  {E.go(c, r, "", SNil{}, z) == UNil{} : UL}

def E.leaf.nil(c, r, z, hl):
  %Equal.sym(Bool, TR(c, r, ""), False{}, leaf.tr(c, r, "", hl)) : {pickc(_, z, UNil{}) == UNil{} : UL}
  {==}

law E.leaf.con.k:
  for +c: Cx
  for +r: R
  for +h: Char
  for t: String
  for +z: U32
  for +hl: T(leafy(r))
  {E.go(c, r, SCon{h, SNil{}}, t, (z + 1 : U32)) == pickc(cmatch(r, code(h)), (z + 1 : U32), UNil{}) : UL}

def E.leaf.con.k(c, r, h, t, z, hl):
  match t:
    case SNil{}:
      Equal.cong(Bool, UL, b => pickc(b, (z + 1 : U32), UNil{}), TR(c, r, SCon{h, SNil{}}), cmatch(r, code(h)), leaf.tr(c, r, SCon{h, SNil{}}, hl))
    case SCon{+a, +t2}:
      %Equal.sym(UL, E.go(c, r, SCon{h, SCon{a, SNil{}}}, t2, ((z + 1 : U32) + 1 : U32)), UNil{}, E.z2(c, r, t2, h, a, SNil{}, ((z + 1 : U32) + 1 : U32), hl)) : {pickc(TR(c, r, SCon{h, SNil{}}), (z + 1 : U32), _) == pickc(cmatch(r, code(h)), (z + 1 : U32), UNil{}) : UL}
      Equal.cong(Bool, UL, b => pickc(b, (z + 1 : U32), UNil{}), TR(c, r, SCon{h, SNil{}}), cmatch(r, code(h)), leaf.tr(c, r, SCon{h, SNil{}}, hl))

law E.leaf.con:
  for +c: Cx
  for +r: R
  for +h: Char
  for +t: String
  for +z: U32
  for +hl: T(leafy(r))
  {E.go(c, r, "", SCon{h, t}, z) == pickc(cmatch(r, code(h)), (z + 1 : U32), UNil{}) : UL}

def E.leaf.con(c, r, h, t, z, hl):
  %Equal.sym(Bool, TR(c, r, ""), False{}, leaf.tr(c, r, "", hl)) : {pickc(_, z, E.go(c, r, SCon{h, SNil{}}, t, (z + 1 : U32))) == pickc(cmatch(r, code(h)), (z + 1 : U32), UNil{}) : UL}
  E.leaf.con.k(c, r, h, t, z, hl)

law not.f:
  for b: Bool
  for +h: T(Bool.not(b))
  {b == False{} : Bool}

def not.f(b, h):
  match b:
    case False{}:
      {==}
    case True{}:
      false.elim({True{} == False{} : Bool}, h)

law leaf.ex.b:
  for b: Bool
  for +z: U32
  T(ex(pickc(b, (z + 1 : U32), UNil{}), single(b, z)))

def leaf.ex.b(b, z):
  match b:
    case True{}:
      same.refl(UCon{(z + 1 : U32), UNil{}})
    case False{}:
      {==}

law leaf.ex.k:
  for +c: Cx
  for +r: R
  for +z: U32
  for +b: Bool
  for x: String
  for +hb: {b == cmatch(r, rdA(c, z)) : Bool}
  for +hl: T(leafy(r))
  for +hne: T(Bool.not(cmatch(r, END)))
  for +hx: T(at(c, x, z))
  T(ex(E.go(c, r, "", x, z), single(b, z)))

law leaf.b.end:
  for +c: Cx
  for +r: R
  for +z: U32
  for b: Bool
  for +hb: {b == cmatch(r, rdA(c, z)) : Bool}
  for +e: T(U32.is_eq(rdA(c, z), END))
  for +hne: T(Bool.not(cmatch(r, END)))
  {b == False{} : Bool}

def leaf.b.end(c, r, z, b, hb, e, hne):
  %Equal.sym(Bool, b, cmatch(r, rdA(c, z)), hb) : {_ == False{} : Bool}
  %Equal.sym(U32, rdA(c, z), END, u32.eq.t(rdA(c, z), END, e)) : {cmatch(r, _) == False{} : Bool}
  not.f(cmatch(r, END), hne)

law leaf.b.con:
  for +c: Cx
  for +r: R
  for +z: U32
  for -b: Bool
  for +h: Char
  for +hb: {b == cmatch(r, rdA(c, z)) : Bool}
  for +e: T(U32.is_eq(rdA(c, z), code(h)))
  {b == cmatch(r, code(h)) : Bool}

def leaf.b.con(c, r, z, b, h, hb, e):
  %u32.eq.t(rdA(c, z), code(h), e) : {b == cmatch(r, _) : Bool}
  hb

law leaf.tr.ex:
  for +c: Cx
  for +r: R
  for +z: U32
  for +b: Bool
  for +h: Char
  for +t: String
  for +eb: {b == cmatch(r, code(h)) : Bool}
  for +hl: T(leafy(r))
  T(ex(E.go(c, r, "", SCon{h, t}, z), single(b, z)))

def leaf.tr.ex(c, r, z, b, h, t, eb, hl):
  %Equal.sym(UL, E.go(c, r, "", SCon{h, t}, z), pickc(cmatch(r, code(h)), (z + 1 : U32), UNil{}), E.leaf.con(c, r, h, t, z, hl)) : T(ex(_, single(b, z)))
  %eb : T(ex(pickc(_, (z + 1 : U32), UNil{}), single(b, z)))
  leaf.ex.b(b, z)

law leaf.nil.ex:
  for +c: Cx
  for +r: R
  for +z: U32
  for +b: Bool
  for +eb: {b == False{} : Bool}
  for +hl: T(leafy(r))
  T(ex(E.go(c, r, "", SNil{}, z), single(b, z)))

def leaf.nil.ex(c, r, z, b, eb, hl):
  %Equal.sym(UL, E.go(c, r, "", SNil{}, z), UNil{}, E.leaf.nil(c, r, z, hl)) : T(ex(_, single(b, z)))
  %Equal.sym(Bool, b, False{}, eb) : T(ex(UNil{}, single(_, z)))
  {==}

def leaf.ex.k(c, r, z, b, x, hb, hl, hne, hx):
  match x:
    case SNil{}:
      leaf.nil.ex(c, r, z, b, leaf.b.end(c, r, z, b, hb, hx, hne), hl)
    case SCon{+h, +t}:
      leaf.tr.ex(c, r, z, b, h, t, leaf.b.con(c, r, z, b, h, hb, at.head(c, h, t, z, hx)), hl)

law leaf.ex:
  for +c: Cx
  for +r: R
  for +z: U32
  for +b: Bool
  for +hb: {b == cmatch(r, rdA(c, z)) : Bool}
  for +hl: T(leafy(r))
  for +hne: T(Bool.not(cmatch(r, END)))
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(ex(E(c, r, z), single(b, z)))

def leaf.ex(c, r, z, b, hb, hl, hne, ga, hc):
  leaf.ex.k(c, r, z, b, suf(c, z), hb, hl, hne, at.suf(c, z, ga, hc))

# empty and failing rules

law E.bad:
  for +c: Cx
  for x: String
  for +p: String
  for +i: U32
  {E.wk(c, Bad{}, x, p, i) == UNil{} : UL}

def E.bad(c, x, p, i):
  match x:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      E.bad(c, t, p ++ SCon{h, SNil{}}, (i + 1 : U32))

law E.emp.tail:
  for +c: Cx
  for x: String
  for +h: Char
  for +t: String
  for +i: U32
  {E.wk(c, Emp{}, x, SCon{h, t}, i) == UNil{} : UL}

def E.emp.tail(c, x, h, t, i):
  match x:
    case SNil{}:
      {==}
    case SCon{+a, +b}:
      E.emp.tail(c, b, h, t ++ SCon{a, SNil{}}, (i + 1 : U32))

law E.emp.go:
  for +c: Cx
  for x: String
  for +i: U32
  T(ex(E.wk(c, Emp{}, x, "", i), VOne{i}))

def E.emp.go(c, x, i):
  match x:
    case SNil{}:
      same.refl(UCon{i, UNil{}})
    case SCon{+h, +t}:
      %Equal.sym(UL, E.wk(c, Emp{}, t, SCon{h, SNil{}}, (i + 1 : U32)), UNil{}, E.emp.tail(c, t, h, SNil{}, (i + 1 : U32))) : T(ex(pickc(True{}, i, _), VOne{i}))
      same.refl(UCon{i, UNil{}})

# alternation

law alt.up.a.k:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +w: U32
  for k: EW(c, a, "", suf(c, z), z, w)
  T(has(w, E(c, Alt{a, b}, z)))

def alt.up.a.k(c, a, b, z, w, k):
  match k:
    case (+q, +y, +e1, e2, ht):
      tr.Eq2(c, Alt{a, b}, q ++ y, z, pos(z, q), w, suf(c, z), e1, e2, E.intro(c, Alt{a, b}, q, "", y, z, or.left(TR(c, a, q), TR(c, b, q), ht)))

law alt.up.b.k:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +w: U32
  for k: EW(c, b, "", suf(c, z), z, w)
  T(has(w, E(c, Alt{a, b}, z)))

def alt.up.b.k(c, a, b, z, w, k):
  match k:
    case (+q, +y, +e1, e2, ht):
      tr.Eq2(c, Alt{a, b}, q ++ y, z, pos(z, q), w, suf(c, z), e1, e2, E.intro(c, Alt{a, b}, q, "", y, z, or.right(TR(c, a, q), TR(c, b, q), ht)))

law alt.down.k:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +w: U32
  for k: EW(c, Alt{a, b}, "", suf(c, z), z, w)
  T(has(w, uapp(E(c, a, z), E(c, b, z))))

def alt.down.k(c, a, b, z, w, k):
  match k:
    case (+q, +y, +e1, e2, ht):
      +e3 = e2
      or.elim(TR(c, a, q), TR(c, b, q), T(has(w, uapp(E(c, a, z), E(c, b, z)))), ht, +h1 => uapp.in.l(w, E(c, a, z), E(c, b, z), tr.Eq2(c, a, q ++ y, z, pos(z, q), w, suf(c, z), e1, e3, E.intro(c, a, q, "", y, z, h1))), +h2 => uapp.in.r(w, E(c, a, z), E(c, b, z), tr.Eq2(c, b, q ++ y, z, pos(z, q), w, suf(c, z), e1, e3, E.intro(c, b, q, "", y, z, h2))))

law alt.up.a:
  for l: UL
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +hl: T(sub(l, E(c, a, z)))
  T(sub(l, E(c, Alt{a, b}, z)))

def alt.up.a(l, c, a, b, z, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, Alt{a, b}, z), alt.up.a.k(c, a, b, z, w, E.elim(c, a, suf(c, z), "", z, w, sub.head(w, t, E(c, a, z), hl))), alt.up.a(t, c, a, b, z, sub.tail(w, t, E(c, a, z), hl)))

law alt.up.b:
  for l: UL
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +hl: T(sub(l, E(c, b, z)))
  T(sub(l, E(c, Alt{a, b}, z)))

def alt.up.b(l, c, a, b, z, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, Alt{a, b}, z), alt.up.b.k(c, a, b, z, w, E.elim(c, b, suf(c, z), "", z, w, sub.head(w, t, E(c, b, z), hl))), alt.up.b(t, c, a, b, z, sub.tail(w, t, E(c, b, z), hl)))

law alt.down:
  for l: UL
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +hl: T(sub(l, E(c, Alt{a, b}, z)))
  T(sub(l, uapp(E(c, a, z), E(c, b, z))))

def alt.down(l, c, a, b, z, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, uapp(E(c, a, z), E(c, b, z)), alt.down.k(c, a, b, z, w, E.elim(c, Alt{a, b}, suf(c, z), "", z, w, sub.head(w, t, E(c, Alt{a, b}, z), hl))), alt.down(t, c, a, b, z, sub.tail(w, t, E(c, Alt{a, b}, z), hl)))

law alt.same:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  T(same(uapp(E(c, a, z), E(c, b, z)), E(c, Alt{a, b}, z)))

def alt.same(c, a, b, z):
  same.i(uapp(E(c, a, z), E(c, b, z)), E(c, Alt{a, b}, z), uapp.sub(E(c, a, z), E(c, b, z), E(c, Alt{a, b}, z), alt.up.a(E(c, a, z), c, a, b, z, sub.refl(E(c, a, z))), alt.up.b(E(c, b, z), c, a, b, z, sub.refl(E(c, b, z)))), alt.down(E(c, Alt{a, b}, z), c, a, b, z, sub.refl(E(c, Alt{a, b}, z))))
# ---- references, and inlining ----

law bi.refl:
  for b: Bool
  T(bi(b, b))

def bi.refl(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law settled.c:
  for +c: Cx
  for +u: String
  for +y: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  {sS(True{}, B0(c), cg(c), u ++ (y ++ v)) == 0n : Nat}

def settled.c(c, u, y, v, h):
  %Equal.sym(String, u ++ (y ++ v), cS(c), h) : {sS(True{}, B0(c), cg(c), _) == 0n : Nat}
  settled(cg(c), cS(c))

law ref.eq:
  for +c: Cx
  for +n: String
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  {TR(c, Ref{n}, y) == TR(c, lk(cg(c), n), y) : Bool}

def ref.eq(c, n, y, u, v, h):
  cong.lk(B0(c), cg(c), cg(c), n, y, ex.S(B0(c), cg(c), u, y, v, settled.c(c, u, y, v, h)))

law cat.sub.l:
  for +u: String
  for +y: String
  for +v: String
  for +x1: String
  for +x2: String
  for -S: String
  for +h: {u ++ (y ++ v) == S : String}
  for +e: {x1 ++ x2 == y : String}
  {u ++ (x1 ++ (x2 ++ v)) == S : String}

def cat.sub.l(u, y, v, x1, x2, S, h, e):
  %app.assoc(x1, x2, v) : {u ++ _ == S : String}
  %Equal.sym(String, x1 ++ x2, y, e) : {u ++ (_ ++ v) == S : String}
  h

law cat.sub.r:
  for +u: String
  for +y: String
  for +v: String
  for +x1: String
  for +x2: String
  for -S: String
  for +h: {u ++ (y ++ v) == S : String}
  for +e: {x1 ++ x2 == y : String}
  {(u ++ x1) ++ (x2 ++ v) == S : String}

def cat.sub.r(u, y, v, x1, x2, S, h, e):
  %app.assoc.sym(u, x1, x2 ++ v) : {_ == S : String}
  cat.sub.l(u, y, v, x1, x2, S, h, e)

law simp.cat.b:
  for +c: Cx
  for y2: R
  for +x: R
  for +s: String
  T(bi(TR(c, simp.cat.k(y2, x), s), TR(c, Cat{x, y2}, s)))

law cat.emp:
  for +c: Cx
  for +x: R
  for +s: String
  T(bi(TR(c, x, s), TR(c, Cat{x, Emp{}}, s)))

law cat.emp.k:
  for +c: Cx
  for +x: R
  for +s: String
  for w: CatW(1n+B0(c), cg(c), x, Emp{}, s, "")
  T(TR(c, x, s))

law cat.emp.eq:
  for +c: Cx
  for +x: R
  for +s1: String
  for +s2: String
  for +s: String
  for +e: {s1 ++ s2 == s : String}
  for +e2: {s2 == "" : String}
  for +ha: T(TR(c, x, s1))
  T(TR(c, x, s))

def cat.emp.eq(c, x, s1, s2, s, e, e2, ha):
  %e : T(TR(c, x, _))
  %Equal.sym(String, s2, "", e2) : T(TR(c, x, s1 ++ _))
  tr.tr(c, x, s1, s1 ++ "", app.nil.sym(s1), ha)

def cat.emp.k(c, x, s, w):
  match w:
    case (+s1, +s2, e, ha, hb):
      cat.emp.eq(c, x, s1, s2, s, e, emp.nil(1n+B0(c), cg(c), s2, hb), ha)

def cat.emp(c, x, s):
  bi.i(TR(c, x, s), TR(c, Cat{x, Emp{}}, s), +h => tr.tr(c, Cat{x, Emp{}}, s ++ "", s, app.nil(s), cat.intro(1n+B0(c), cg(c), x, Emp{}, s, "", "", h, {==})), +h => cat.emp.k(c, x, s, cat.elim(1n+B0(c), cg(c), x, Emp{}, s, "", h)))

law simp.alt.b:
  for +c: Cx
  for y2: R
  for +x: R
  for +s: String
  T(bi(TR(c, simp.alt.k(y2, x), s), TR(c, Alt{x, y2}, s)))

law alt.bad:
  for +c: Cx
  for +x: R
  for +s: String
  T(bi(TR(c, x, s), TR(c, Alt{x, Bad{}}, s)))

law or.false:
  for a: Bool
  T(bi(a, orelse(a, u => False{})))

def or.false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def alt.bad(c, x, s):
  or.false(TR(c, x, s))

def simp.cat.b(c, y2, x, s):
  match y2:
    case Emp{}:
      cat.emp(c, x, s)
    case Bad{}:
      bi.refl(TR(c, Cat{x, Bad{}}, s))
    case Lit{+c0}:
      bi.refl(TR(c, Cat{x, Lit{c0}}, s))
    case Rng{+p0, +p1}:
      bi.refl(TR(c, Cat{x, Rng{p0, p1}}, s))
    case Cat{+p0, +p1}:
      bi.refl(TR(c, Cat{x, Cat{p0, p1}}, s))
    case Alt{+p0, +p1}:
      bi.refl(TR(c, Cat{x, Alt{p0, p1}}, s))
    case Star{+p0}:
      bi.refl(TR(c, Cat{x, Star{p0}}, s))
    case Ref{+p0}:
      bi.refl(TR(c, Cat{x, Ref{p0}}, s))

def simp.alt.b(c, y2, x, s):
  match y2:
    case Emp{}:
      bi.refl(TR(c, Alt{x, Emp{}}, s))
    case Bad{}:
      alt.bad(c, x, s)
    case Lit{+c0}:
      bi.refl(TR(c, Alt{x, Lit{c0}}, s))
    case Rng{+p0, +p1}:
      bi.refl(TR(c, Alt{x, Rng{p0, p1}}, s))
    case Cat{+p0, +p1}:
      bi.refl(TR(c, Alt{x, Cat{p0, p1}}, s))
    case Alt{+p0, +p1}:
      bi.refl(TR(c, Alt{x, Alt{p0, p1}}, s))
    case Star{+p0}:
      bi.refl(TR(c, Alt{x, Star{p0}}, s))
    case Ref{+p0}:
      bi.refl(TR(c, Alt{x, Ref{p0}}, s))

law bi.trans:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +h1: T(bi(a, b))
  for +h2: T(bi(b, c))
  T(bi(a, c))

def bi.trans(a, b, c, h1, h2):
  bi.i(a, c, +ha => bi.lr(b, c, h2, bi.lr(a, b, h1, ha)), +hc => bi.rl(a, b, h1, bi.rl(b, c, h2, hc)))

law bi.eq:
  for a: Bool
  for b: Bool
  for +h: T(bi(a, b))
  {a == b : Bool}

def bi.eq(a, b, h):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      false.elim({False{} == True{} : Bool}, h)
    case True{} False{}:
      false.elim({True{} == False{} : Bool}, h)
    case True{} True{}:
      {==}

law bi.of.eq:
  for a: Bool
  for -b: Bool
  for +e: {a == b : Bool}
  T(bi(a, b))

def bi.of.eq(a, b, e):
  %e : T(bi(a, _))
  bi.refl(a)

law or.cong:
  for +a1: Bool
  for +b1: Bool
  for +a2: Bool
  for +b2: Bool
  for +h1: T(bi(a1, a2))
  for +h2: T(bi(b1, b2))
  T(bi(orelse(a1, u => b1), orelse(a2, u => b2)))

def or.cong(a1, b1, a2, b2, h1, h2):
  %bi.eq(a1, a2, h1) : T(bi(orelse(a1, u => b1), orelse(_, u => b2)))
  %bi.eq(b1, b2, h2) : T(bi(orelse(a1, u => b1), orelse(a1, u => _)))
  bi.refl(orelse(a1, u => b1))

def cat.cong.w(+c: Cx, +a1: R, +b1: R, +a2: R, +b2: R, +y: String, w: CatW(1n+B0(c), cg(c), a1, b1, y, ""), ia: @s1: String -> @s2: String -> {s1 ++ s2 == y : String} -> T(TR(c, a1, s1)) -> T(TR(c, a2, s1)), ib: @s1: String -> @s2: String -> {s1 ++ s2 == y : String} -> T(TR(c, b1, s2)) -> T(TR(c, b2, s2))) -> T(TR(c, Cat{a2, b2}, y)):
  match w:
    case (+s1, +s2, e, ha, hb):
      +e2 = e
      tr.tr(c, Cat{a2, b2}, s1 ++ s2, y, e2, cat.intro(1n+B0(c), cg(c), a2, b2, s1, s2, "", ia(s1, s2, e2, ha), ib(s1, s2, e2, hb)))

def seq.cong.w(+c: Cx, +a1: R, +b1: R, +a2: R, +b2: R, +y: String, w: Seq2W(1n+B0(c), cg(c), a1, b1, y), ia: @s1: String -> @s2: String -> {s1 ++ s2 == y : String} -> T(TR(c, a1, s1)) -> T(TR(c, a2, s1)), ib: @s1: String -> @s2: String -> {s1 ++ s2 == y : String} -> T(sem(1n+B0(c), cg(c), b1, s2, "")) -> T(sem(1n+B0(c), cg(c), b2, s2, ""))) -> T(sem(1n+B0(c), cg(c), Cat{a2, Cat{b2, Emp{}}}, y, "")):
  match w:
    case (+s1, +s2, e, ha, hb):
      +e2 = e
      tr.x(1n+B0(c), cg(c), Cat{a2, Cat{b2, Emp{}}}, s1 ++ s2, y, e2, seq2.intro(1n+B0(c), cg(c), a2, b2, s1, s2, ia(s1, s2, e2, ha), ib(s1, s2, e2, hb)))

def star.cong.w(+c: Cx, +a1: R, +a2: R, +y: String, w: ExW(1n+B0(c), cg(c), a1, y), k: @m: Nat -> T(sem(1n+B0(c), cg(c), exact(m, a1), y, "")) -> T(sem(1n+B0(c), cg(c), exact(m, a2), y, ""))) -> T(TR(c, Star{a2}, y)):
  match w:
    case (+m, hm):
      star.intro(m, 1n+B0(c), cg(c), a2, y, k(m, hm))

law inl.k.ok:
  for +c: Cx
  for +n: String
  for +y: String
  for b: Bool
  for +X: R
  for +hb: T(bi(TR(c, X, y), TR(c, Ref{n}, y)))
  T(bi(TR(c, inl.k(b, n, u => X), y), TR(c, Ref{n}, y)))

def inl.k.ok(c, n, y, b, X, hb):
  match b:
    case True{}:
      bi.refl(TR(c, Ref{n}, y))
    case False{}:
      hb

def stt(+c: Cx, +fl: Nat, k: Nat, +r: R, +m: Nat, +y: String) -> Bool:
  match k:
    case 0n:
      match r:
        case Star{+a}:
          bi(sem(1n+B0(c), cg(c), exact(m, inl(fl, cg(c), a)), y, ""), sem(1n+B0(c), cg(c), exact(m, a), y, ""))
        case Emp{}:
          True{}
        case Bad{}:
          True{}
        case Lit{c0}:
          True{}
        case Rng{p0, p1}:
          True{}
        case Cat{p0, p1}:
          True{}
        case Alt{p0, p1}:
          True{}
        case Ref{p0}:
          True{}
    case 1n+j:
      bi(TR(c, inl(fl, cg(c), r), y), TR(c, r, y))

law ie:
  for +c: Cx
  for +fl: Nat
  for +r: R
  for +k: Nat
  for +m: Nat
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  T(stt(c, fl, k, r, m, y))

def ie(c, fl, r, k, m, y, u, v, h):
  match fl:
    case 0n:
      match r:
        case Star{+a}:
          match k:
            case 0n:
              bi.refl(sem(1n+B0(c), cg(c), exact(m, a), y, ""))
            case 1n+j:
              bi.refl(TR(c, Star{a}, y))
        case Emp{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Emp{}, y))
        case Bad{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Bad{}, y))
        case Lit{+c0}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Lit{c0}, y))
        case Rng{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Rng{p0, p1}, y))
        case Cat{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Cat{p0, p1}, y))
        case Alt{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Alt{p0, p1}, y))
        case Ref{+p0}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Ref{p0}, y))
    case 1n+p:
      match r:
        case Star{+a}:
          match k:
            case 0n:
              match m:
                case 0n:
                  bi.refl(sem(1n+B0(c), cg(c), Emp{}, y, ""))
                case 1n+i:
                  bi.i(sem(1n+B0(c), cg(c), Cat{inl(fl, cg(c), a), Cat{exact(i, inl(fl, cg(c), a)), Emp{}}}, y, ""), sem(1n+B0(c), cg(c), Cat{a, Cat{exact(i, a), Emp{}}}, y, ""), +hh => seq.cong.w(c, inl(fl, cg(c), a), exact(i, inl(fl, cg(c), a)), a, exact(i, a), y, seq2.elim(1n+B0(c), cg(c), inl(fl, cg(c), a), exact(i, inl(fl, cg(c), a)), y, hh), +s1 => +s2 => +e => +ha => bi.lr(TR(c, inl(fl, cg(c), a), s1), TR(c, a, s1), ie(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, y, v, s1, s2, cS(c), h, e)), ha), +s1 => +s2 => +e => +hb => bi.lr(sem(1n+B0(c), cg(c), exact(i, inl(fl, cg(c), a)), s2, ""), sem(1n+B0(c), cg(c), exact(i, a), s2, ""), ie(c, fl, Star{a}, 0n, i, s2, u ++ s1, v, cat.sub.r(u, y, v, s1, s2, cS(c), h, e)), hb)), +hh => seq.cong.w(c, a, exact(i, a), inl(fl, cg(c), a), exact(i, inl(fl, cg(c), a)), y, seq2.elim(1n+B0(c), cg(c), a, exact(i, a), y, hh), +s1 => +s2 => +e => +ha => bi.rl(TR(c, inl(fl, cg(c), a), s1), TR(c, a, s1), ie(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, y, v, s1, s2, cS(c), h, e)), ha), +s1 => +s2 => +e => +hb => bi.rl(sem(1n+B0(c), cg(c), exact(i, inl(fl, cg(c), a)), s2, ""), sem(1n+B0(c), cg(c), exact(i, a), s2, ""), ie(c, fl, Star{a}, 0n, i, s2, u ++ s1, v, cat.sub.r(u, y, v, s1, s2, cS(c), h, e)), hb)))
            case 1n+j:
              match j:
                case 0n:
                  bi.i(TR(c, Star{inl(fl, cg(c), a)}, y), TR(c, Star{a}, y), +hh => star.cong.w(c, inl(fl, cg(c), a), a, y, star.elim(1n+B0(c), cg(c), inl(fl, cg(c), a), y, "", hh), +mm => +hm => bi.lr(sem(1n+B0(c), cg(c), exact(mm, inl(fl, cg(c), a)), y, ""), sem(1n+B0(c), cg(c), exact(mm, a), y, ""), ie(c, fl, Star{a}, j, mm, y, u, v, h), hm)), +hh => star.cong.w(c, a, inl(fl, cg(c), a), y, star.elim(1n+B0(c), cg(c), a, y, "", hh), +mm => +hm => bi.rl(sem(1n+B0(c), cg(c), exact(mm, inl(fl, cg(c), a)), y, ""), sem(1n+B0(c), cg(c), exact(mm, a), y, ""), ie(c, fl, Star{a}, j, mm, y, u, v, h), hm)))
                case 1n+j2:
                  ie(c, fl, Star{a}, j, m, y, u, v, h)
        case Emp{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Emp{}, y))
        case Bad{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Bad{}, y))
        case Lit{+c0}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Lit{c0}, y))
        case Rng{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.refl(TR(c, Rng{p0, p1}, y))
        case Cat{+a, +b}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.trans(TR(c, simp.cat.k(inl(fl, cg(c), b), inl(fl, cg(c), a)), y), TR(c, Cat{inl(fl, cg(c), a), inl(fl, cg(c), b)}, y), TR(c, Cat{a, b}, y), simp.cat.b(c, inl(fl, cg(c), b), inl(fl, cg(c), a), y), bi.i(TR(c, Cat{inl(fl, cg(c), a), inl(fl, cg(c), b)}, y), TR(c, Cat{a, b}, y), +hh => cat.cong.w(c, inl(fl, cg(c), a), inl(fl, cg(c), b), a, b, y, cat.elim(1n+B0(c), cg(c), inl(fl, cg(c), a), inl(fl, cg(c), b), y, "", hh), +s1 => +s2 => +e => +ha => bi.lr(TR(c, inl(fl, cg(c), a), s1), TR(c, a, s1), ie(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, y, v, s1, s2, cS(c), h, e)), ha), +s1 => +s2 => +e => +hb => bi.lr(TR(c, inl(fl, cg(c), b), s2), TR(c, b, s2), ie(c, fl, b, 1n, 0n, s2, u ++ s1, v, cat.sub.r(u, y, v, s1, s2, cS(c), h, e)), hb)), +hh => cat.cong.w(c, a, b, inl(fl, cg(c), a), inl(fl, cg(c), b), y, cat.elim(1n+B0(c), cg(c), a, b, y, "", hh), +s1 => +s2 => +e => +ha => bi.rl(TR(c, inl(fl, cg(c), a), s1), TR(c, a, s1), ie(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, y, v, s1, s2, cS(c), h, e)), ha), +s1 => +s2 => +e => +hb => bi.rl(TR(c, inl(fl, cg(c), b), s2), TR(c, b, s2), ie(c, fl, b, 1n, 0n, s2, u ++ s1, v, cat.sub.r(u, y, v, s1, s2, cS(c), h, e)), hb))))
        case Alt{+a, +b}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              bi.trans(TR(c, simp.alt.k(inl(fl, cg(c), b), inl(fl, cg(c), a)), y), TR(c, Alt{inl(fl, cg(c), a), inl(fl, cg(c), b)}, y), TR(c, Alt{a, b}, y), simp.alt.b(c, inl(fl, cg(c), b), inl(fl, cg(c), a), y), or.cong(TR(c, inl(fl, cg(c), a), y), TR(c, inl(fl, cg(c), b), y), TR(c, a, y), TR(c, b, y), ie(c, fl, a, 1n, 0n, y, u, v, h), ie(c, fl, b, 1n, 0n, y, u, v, h)))
        case Ref{+n}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              inl.k.ok(c, n, y, is_rec(cg(c), n), inl(p, cg(c), lk(cg(c), n)), bi.trans(TR(c, inl(p, cg(c), lk(cg(c), n)), y), TR(c, lk(cg(c), n), y), TR(c, Ref{n}, y), ie(c, p, lk(cg(c), n), 1n, 0n, y, u, v, h), bi.of.eq(TR(c, lk(cg(c), n), y), TR(c, Ref{n}, y), Equal.sym(Bool, TR(c, Ref{n}, y), TR(c, lk(cg(c), n), y), ref.eq(c, n, y, u, v, h)))))

law inl.eq:
  for +c: Cx
  for +fl: Nat
  for +r: R
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  T(bi(TR(c, inl(fl, cg(c), r), y), TR(c, r, y)))

def inl.eq(c, fl, r, y, u, v, h):
  ie(c, fl, r, 1n, 0n, y, u, v, h)
# ---- from rules back to grammars ----

law lk.pick.bi:
  for +c: Cx
  for e: Bool
  for +r1: R
  for +r2: R
  for +t1: R
  for +t2: R
  for +y: String
  for +h1: T(bi(TR(c, r1, y), TR(c, r2, y)))
  for +h2: T(bi(TR(c, t1, y), TR(c, t2, y)))
  T(bi(TR(c, lk.pick(e, r1, t1), y), TR(c, lk.pick(e, r2, t2), y)))

def lk.pick.bi(c, e, r1, r2, t1, t2, y, h1, h2):
  match e:
    case False{}:
      h2
    case True{}:
      or.cong(TR(c, r1, y), TR(c, t1, y), TR(c, r2, y), TR(c, t2, y), h1, h2)

law lk.inlg.eq:
  for l: Gram
  for +c: Cx
  for +fl: Nat
  for +n: String
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  T(bi(TR(c, lk(inlg(fl, cg(c), l), n), y), TR(c, lk(l, n), y)))

def lk.inlg.eq(l, c, fl, n, y, u, v, h):
  match l:
    case GNil{}:
      bi.refl(TR(c, Bad{}, y))
    case GCon{+k, +r, +t}:
      lk.pick.bi(c, String.eq(String.to_lower(k), String.to_lower(n)), inl(fl, cg(c), r), r, lk(inlg(fl, cg(c), t), n), lk(t, n), y, inl.eq(c, fl, r, y, u, v, h), lk.inlg.eq(t, c, fl, n, y, u, v, h))

law lk.name:
  for g: Gram
  for +k: String
  for +n: String
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  {lk(g, k) == lk(g, n) : R}

def lk.name(g, k, n, e):
  match g:
    case GNil{}:
      {==}
    case GCon{+k2, +r, +t}:
      %str.eq.t(String.to_lower(k), String.to_lower(n), e) : {lk.pick(String.eq(String.to_lower(k2), String.to_lower(k)), r, lk(t, k)) == lk.pick(String.eq(String.to_lower(k2), _), r, lk(t, n)) : R}
      %lk.name(t, k, n, e) : {lk.pick(String.eq(String.to_lower(k2), String.to_lower(k)), r, lk(t, k)) == lk.pick(String.eq(String.to_lower(k2), String.to_lower(k)), r, _) : R}
      {==}

law simp0.bi:
  for +c: Cx
  for r: R
  for +y: String
  T(bi(TR(c, simp0(r), y), TR(c, r, y)))

def simp0.bi(c, r, y):
  match r:
    case Emp{}:
      bi.refl(TR(c, Emp{}, y))
    case Bad{}:
      bi.refl(TR(c, Bad{}, y))
    case Lit{+c0}:
      bi.refl(TR(c, Lit{c0}, y))
    case Rng{+p0, +p1}:
      bi.refl(TR(c, Rng{p0, p1}, y))
    case Cat{+p0, +p1}:
      bi.refl(TR(c, Cat{p0, p1}, y))
    case Star{+p0}:
      bi.refl(TR(c, Star{p0}, y))
    case Ref{+p0}:
      bi.refl(TR(c, Ref{p0}, y))
    case Alt{+a, b}:
      match b:
        case Emp{}:
          bi.refl(TR(c, Alt{a, Emp{}}, y))
        case Bad{}:
          alt.bad(c, a, y)
        case Lit{+c0}:
          bi.refl(TR(c, Alt{a, Lit{c0}}, y))
        case Rng{+p0, +p1}:
          bi.refl(TR(c, Alt{a, Rng{p0, p1}}, y))
        case Cat{+p0, +p1}:
          bi.refl(TR(c, Alt{a, Cat{p0, p1}}, y))
        case Alt{+p0, +p1}:
          bi.refl(TR(c, Alt{a, Alt{p0, p1}}, y))
        case Star{+p0}:
          bi.refl(TR(c, Alt{a, Star{p0}}, y))
        case Ref{+p0}:
          bi.refl(TR(c, Alt{a, Ref{p0}}, y))

law ref.bi:
  for +c: Cx
  for +k: String
  for +n: String
  for +y: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == cS(c) : String}
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  T(bi(TR(c, body(cg2(c), k), y), TR(c, Ref{n}, y)))

def ref.bi(c, k, n, y, u, v, h, e):
  %Equal.sym(R, lk(cg2(c), k), lk(cg2(c), n), lk.name(cg2(c), k, n, e)) : T(bi(TR(c, simp0(_), y), TR(c, Ref{n}, y)))
  bi.trans(TR(c, simp0(lk(cg2(c), n)), y), TR(c, lk(cg2(c), n), y), TR(c, Ref{n}, y), simp0.bi(c, lk(cg2(c), n), y), bi.trans(TR(c, lk(cg2(c), n), y), TR(c, lk(cg(c), n), y), TR(c, Ref{n}, y), lk.inlg.eq(cg(c), c, 12n, n, y, u, v, h), bi.of.eq(TR(c, lk(cg(c), n), y), TR(c, Ref{n}, y), Equal.sym(Bool, TR(c, Ref{n}, y), TR(c, lk(cg(c), n), y), ref.eq(c, n, y, u, v, h)))))
# ---- references at cells ----

law E.rb.up.k2:
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +w: U32
  for +q: String
  for +y: String
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for +e1: {q ++ y == suf(c, z) : String}
  for +e2: {pos(z, q) == w : U32}
  for +ht: T(TR(c, body(cg2(c), k), q))
  for wit: CellW(c, z)
  T(has(w, E(c, Ref{n}, z)))

law sub.of.cell:
  for +c: Cx
  for +u: String
  for +q: String
  for +y: String
  for -z: U32
  for +eu: {u ++ suf(c, z) == cS(c) : String}
  for +e1: {q ++ y == suf(c, z) : String}
  {u ++ (q ++ y) == cS(c) : String}

def sub.of.cell(c, u, q, y, z, eu, e1):
  %Equal.sym(String, q ++ y, suf(c, z), e1) : {u ++ _ == cS(c) : String}
  eu

def E.rb.up.k2(c, k, n, z, w, q, y, e, e1, e2, ht, wit):
  match wit:
    case (+u, +eu, ep):
      tr.Eq2(c, Ref{n}, q ++ y, z, pos(z, q), w, suf(c, z), e1, e2, E.intro(c, Ref{n}, q, "", y, z, bi.lr(TR(c, body(cg2(c), k), q), TR(c, Ref{n}, q), ref.bi(c, k, n, q, u, y, sub.of.cell(c, u, q, y, z, eu, e1), e), ht)))

law E.rb.up.k1:
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +w: U32
  for +hc: T(cell(c, z))
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for h: EW(c, body(cg2(c), k), "", suf(c, z), z, w)
  T(has(w, E(c, Ref{n}, z)))

def E.rb.up.k1(c, k, n, z, w, hc, e, h):
  match h:
    case (+q, +y, +e1, e2, ht):
      E.rb.up.k2(c, k, n, z, w, q, y, e, e1, e2, ht, cell.elim(c, z, hc))

law E.rb.up:
  for l: UL
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +hc: T(cell(c, z))
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for +hl: T(sub(l, E(c, body(cg2(c), k), z)))
  T(sub(l, E(c, Ref{n}, z)))

def E.rb.up(l, c, k, n, z, hc, e, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, Ref{n}, z), E.rb.up.k1(c, k, n, z, w, hc, e, E.elim(c, body(cg2(c), k), suf(c, z), "", z, w, sub.head(w, t, E(c, body(cg2(c), k), z), hl))), E.rb.up(t, c, k, n, z, hc, e, sub.tail(w, t, E(c, body(cg2(c), k), z), hl)))

law E.rb.down.k2:
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +w: U32
  for +q: String
  for +y: String
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for +e1: {q ++ y == suf(c, z) : String}
  for +e2: {pos(z, q) == w : U32}
  for +ht: T(TR(c, Ref{n}, q))
  for wit: CellW(c, z)
  T(has(w, E(c, body(cg2(c), k), z)))

def E.rb.down.k2(c, k, n, z, w, q, y, e, e1, e2, ht, wit):
  match wit:
    case (+u, +eu, ep):
      tr.Eq2(c, body(cg2(c), k), q ++ y, z, pos(z, q), w, suf(c, z), e1, e2, E.intro(c, body(cg2(c), k), q, "", y, z, bi.rl(TR(c, body(cg2(c), k), q), TR(c, Ref{n}, q), ref.bi(c, k, n, q, u, y, sub.of.cell(c, u, q, y, z, eu, e1), e), ht)))

law E.rb.down.k1:
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +w: U32
  for +hc: T(cell(c, z))
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for h: EW(c, Ref{n}, "", suf(c, z), z, w)
  T(has(w, E(c, body(cg2(c), k), z)))

def E.rb.down.k1(c, k, n, z, w, hc, e, h):
  match h:
    case (+q, +y, +e1, e2, ht):
      E.rb.down.k2(c, k, n, z, w, q, y, e, e1, e2, ht, cell.elim(c, z, hc))

law E.rb.down:
  for l: UL
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +hc: T(cell(c, z))
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  for +hl: T(sub(l, E(c, Ref{n}, z)))
  T(sub(l, E(c, body(cg2(c), k), z)))

def E.rb.down(l, c, k, n, z, hc, e, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, E(c, body(cg2(c), k), z), E.rb.down.k1(c, k, n, z, w, hc, e, E.elim(c, Ref{n}, suf(c, z), "", z, w, sub.head(w, t, E(c, Ref{n}, z), hl))), E.rb.down(t, c, k, n, z, hc, e, sub.tail(w, t, E(c, Ref{n}, z), hl)))

law E.ref.same:
  for +c: Cx
  for +k: String
  for +n: String
  for +z: U32
  for +hc: T(cell(c, z))
  for +e: T(String.eq(String.to_lower(k), String.to_lower(n)))
  T(same(E(c, body(cg2(c), k), z), E(c, Ref{n}, z)))

def E.ref.same(c, k, n, z, hc, e):
  same.i(E(c, body(cg2(c), k), z), E(c, Ref{n}, z), E.rb.up(E(c, body(cg2(c), k), z), c, k, n, z, hc, e, sub.refl(E(c, body(cg2(c), k), z))), E.rb.down(E(c, Ref{n}, z), c, k, n, z, hc, e, sub.refl(E(c, Ref{n}, z))))
# ---- guards: a rule that matches at a cell can start with that cell's character ----

def fi(+fl: Nat, +g: Gram, +r: R, q: String) -> Bool:
  match q:
    case SNil{}:
      nul(fl, g, r)
    case SCon{+h, t}:
      fst(fl, g, r, code(h))

def fh(+c: Cx, k: Nat, +r: R, +m: Nat, +q: String) -> Bool:
  match k:
    case 0n:
      match r:
        case Star{+a}:
          sem(1n+B0(c), cg(c), exact(m, a), q, "")
        case Emp{}:
          True{}
        case Bad{}:
          True{}
        case Lit{c0}:
          True{}
        case Rng{p0, p1}:
          True{}
        case Cat{p0, p1}:
          True{}
        case Alt{p0, p1}:
          True{}
        case Ref{p0}:
          True{}
    case 1n+j:
      TR(c, r, q)

def co(+c: Cx, +fl: Nat, k: Nat, +r: R, +q: String) -> Bool:
  match k:
    case 0n:
      match r:
        case Star{+a}:
          fi(fl, cg2(c), Star{a}, q)
        case Emp{}:
          True{}
        case Bad{}:
          True{}
        case Lit{c0}:
          True{}
        case Rng{p0, p1}:
          True{}
        case Cat{p0, p1}:
          True{}
        case Alt{p0, p1}:
          True{}
        case Ref{p0}:
          True{}
    case 1n+j:
      fi(fl, cg2(c), r, q)

law fi.star.k2:
  for +c: Cx
  for +p: Nat
  for +a: R
  for x1: String
  for +x2: String
  for +ih1: T(fi(1n+p, cg2(c), a, x1))
  for +ih2: T(fi(1n+p, cg2(c), Star{a}, x2))
  T(fi(1n+p, cg2(c), Star{a}, x1 ++ x2))

def fi.star.k2(c, p, a, x1, x2, ih1, ih2):
  match x1:
    case SNil{}:
      ih2
    case SCon{+h, +t}:
      ih1

law fi.star.k:
  for +c: Cx
  for +p: Nat
  for +a: R
  for +x1: String
  for +x2: String
  for +q: String
  for +e: {x1 ++ x2 == q : String}
  for +ih1: T(fi(1n+p, cg2(c), a, x1))
  for +ih2: T(fi(1n+p, cg2(c), Star{a}, x2))
  T(fi(1n+p, cg2(c), Star{a}, q))

def fi.star.k(c, p, a, x1, x2, q, e, ih1, ih2):
  %e : T(fi(1n+p, cg2(c), Star{a}, _))
  fi.star.k2(c, p, a, x1, x2, ih1, ih2)

def fi.star.w(+c: Cx, +fl: Nat, +a: R, +q: String, w: ExW(1n+B0(c), cg(c), a, q), f: @m: Nat -> T(sem(1n+B0(c), cg(c), exact(m, a), q, "")) -> T(fi(fl, cg2(c), Star{a}, q))) -> T(fi(fl, cg2(c), Star{a}, q)):
  match w:
    case (+m, hm):
      f(m, hm)

law fi.cat.k2:
  for +c: Cx
  for +p: Nat
  for +a: R
  for +b: R
  for s1: String
  for s2: String
  for +ia: T(fi(1n+p, cg2(c), a, s1))
  for +ib: T(fi(1n+p, cg2(c), b, s2))
  T(fi(1n+p, cg2(c), Cat{a, b}, s1 ++ s2))

def fi.cat.k2(c, p, a, b, s1, s2, ia, ib):
  match s1:
    case SNil{}:
      match s2:
        case SNil{}:
          and.i(nul(1n+p, cg2(c), a), nul(1n+p, cg2(c), b), ia, ib)
        case SCon{+h, +t}:
          or.r(fst(1n+p, cg2(c), a, code(h)), Bool.and(nul(1n+p, cg2(c), a), fst(1n+p, cg2(c), b, code(h))), and.i(nul(1n+p, cg2(c), a), fst(1n+p, cg2(c), b, code(h)), ia, ib))
    case SCon{+h, +t}:
      or.l(fst(1n+p, cg2(c), a, code(h)), Bool.and(nul(1n+p, cg2(c), a), fst(1n+p, cg2(c), b, code(h))), ia)

law fi.cat.k:
  for +c: Cx
  for +p: Nat
  for +a: R
  for +b: R
  for +s1: String
  for +s2: String
  for +q: String
  for +e: {s1 ++ s2 == q : String}
  for +ia: T(fi(1n+p, cg2(c), a, s1))
  for +ib: T(fi(1n+p, cg2(c), b, s2))
  T(fi(1n+p, cg2(c), Cat{a, b}, q))

def fi.cat.k(c, p, a, b, s1, s2, q, e, ia, ib):
  %e : T(fi(1n+p, cg2(c), Cat{a, b}, _))
  fi.cat.k2(c, p, a, b, s1, s2, ia, ib)

def fi.cat.w(+c: Cx, +p: Nat, +a: R, +b: R, +q: String, w: CatW(1n+B0(c), cg(c), a, b, q, ""), ka: @s1: String -> @s2: String -> {s1 ++ s2 == q : String} -> T(TR(c, a, s1)) -> T(fi(1n+p, cg2(c), a, s1)), kb: @s1: String -> @s2: String -> {s1 ++ s2 == q : String} -> T(TR(c, b, s2)) -> T(fi(1n+p, cg2(c), b, s2))) -> T(fi(1n+p, cg2(c), Cat{a, b}, q)):
  match w:
    case (+s1, +s2, e, ha, hb):
      +e2 = e
      fi.cat.k(c, p, a, b, s1, s2, q, e2, ka(s1, s2, e2, ha), kb(s1, s2, e2, hb))

law fi.alt.l:
  for +c: Cx
  for +p: Nat
  for +a: R
  for +b: R
  for q: String
  for +h: T(fi(1n+p, cg2(c), a, q))
  T(fi(1n+p, cg2(c), Alt{a, b}, q))

def fi.alt.l(c, p, a, b, q, h):
  match q:
    case SNil{}:
      or.l(nul(1n+p, cg2(c), a), nul(1n+p, cg2(c), b), h)
    case SCon{+x, +t}:
      or.l(fst(1n+p, cg2(c), a, code(x)), fst(1n+p, cg2(c), b, code(x)), h)

law fi.alt.r:
  for +c: Cx
  for +p: Nat
  for +a: R
  for +b: R
  for q: String
  for +h: T(fi(1n+p, cg2(c), b, q))
  T(fi(1n+p, cg2(c), Alt{a, b}, q))

def fi.alt.r(c, p, a, b, q, h):
  match q:
    case SNil{}:
      or.r(nul(1n+p, cg2(c), a), nul(1n+p, cg2(c), b), h)
    case SCon{+x, +t}:
      or.r(fst(1n+p, cg2(c), a, code(x)), fst(1n+p, cg2(c), b, code(x)), h)

law fi.ref:
  for +c: Cx
  for +p: Nat
  for +n: String
  for q: String
  for +h: T(fi(p, cg2(c), lk(cg2(c), n), q))
  T(fi(1n+p, cg2(c), Ref{n}, q))

def fi.ref(c, p, n, q, h):
  match q:
    case SNil{}:
      h
    case SCon{+x, +t}:
      h

law fi.zero:
  for +c: Cx
  for +r: R
  for q: String
  T(fi(0n, cg2(c), r, q))

def fi.zero(c, r, q):
  match q:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      {==}

law ref.down:
  for +c: Cx
  for +n: String
  for +q: String
  for +u: String
  for +v: String
  for +h: {u ++ (q ++ v) == cS(c) : String}
  for +hy: T(TR(c, Ref{n}, q))
  T(TR(c, lk(cg2(c), n), q))

def ref.down(c, n, q, u, v, h, hy):
  bi.rl(TR(c, lk(cg2(c), n), q), TR(c, lk(cg(c), n), q), lk.inlg.eq(cg(c), c, 12n, n, q, u, v, h), bi.lr(TR(c, Ref{n}, q), TR(c, lk(cg(c), n), q), bi.of.eq(TR(c, Ref{n}, q), TR(c, lk(cg(c), n), q), ref.eq(c, n, q, u, v, h)), hy))

law tr.fi:
  for +c: Cx
  for +fl: Nat
  for +r: R
  for -x: String
  for +y: String
  for +e: {x == y : String}
  for +h: T(fi(fl, cg2(c), r, x))
  T(fi(fl, cg2(c), r, y))

def tr.fi(c, fl, r, x, y, e, h):
  %e : T(fi(fl, cg2(c), r, _))
  h

law fi.ok:
  for +c: Cx
  for +fl: Nat
  for +r: R
  for +k: Nat
  for +m: Nat
  for +q: String
  for +u: String
  for +v: String
  for +h: {u ++ (q ++ v) == cS(c) : String}
  for +hy: T(fh(c, k, r, m, q))
  T(co(c, fl, k, r, q))

def fi.ok(c, fl, r, k, m, q, u, v, h, hy):
  match fl:
    case 0n:
      match r:
        case Star{+a}:
          match k:
            case 0n:
              fi.zero(c, Star{a}, q)
            case 1n+j:
              fi.zero(c, Star{a}, q)
        case Emp{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Emp{}, q)
        case Bad{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Bad{}, q)
        case Lit{+c0}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Lit{c0}, q)
        case Rng{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Rng{p0, p1}, q)
        case Cat{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Cat{p0, p1}, q)
        case Alt{+p0, +p1}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Alt{p0, p1}, q)
        case Ref{+p0}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.zero(c, Ref{p0}, q)
    case 1n+p:
      match r:
        case Star{+a}:
          match k:
            case 0n:
              match m:
                case 0n:
                  tr.fi(c, fl, Star{a}, "", q, Equal.sym(String, q, "", emp.nil(1n+B0(c), cg(c), q, hy)), {==})
                case 1n+i:
                  seq2.with(1n+B0(c), cg(c), a, exact(i, a), q, seq2.elim(1n+B0(c), cg(c), a, exact(i, a), q, hy), T(fi(fl, cg2(c), Star{a}, q)), +s1 => +s2 => +e => +h1 => +h2 => fi.star.k(c, p, a, s1, s2, q, e, fi.ok(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, q, v, s1, s2, cS(c), h, e), h1), fi.ok(c, fl, Star{a}, k, i, s2, u ++ s1, v, cat.sub.r(u, q, v, s1, s2, cS(c), h, e), h2)))
            case 1n+j:
              match j:
                case 0n:
                  fi.star.w(c, fl, a, q, star.elim(1n+B0(c), cg(c), a, q, "", hy), +mm => +hm => fi.ok(c, fl, Star{a}, j, mm, q, u, v, h, hm))
                case 1n+j2:
                  fi.ok(c, fl, Star{a}, j, m, q, u, v, h, hy)
        case Emp{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              match q:
                case SNil{}:
                  {==}
                case SCon{+x, +t}:
                  false.elim(T(False{}), hy)
        case Bad{}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              false.elim(T(fi(fl, cg2(c), Bad{}, q)), hy)
        case Lit{+x}:
          match x:
            case Chr{+a}:
              match k:
                case 0n:
                  {==}
                case 1n+j:
                  match q:
                    case SNil{}:
                      false.elim(T(False{}), hy)
                    case SCon{+h1, +t}:
                      match h1:
                        case Chr{+b}:
                          match t:
                            case SNil{}:
                              hy
                            case SCon{+h2, +t2}:
                              false.elim(T(U32.is_eq(a, b)), hy)
        case Rng{+lo, +hi}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              match q:
                case SNil{}:
                  false.elim(T(False{}), hy)
                case SCon{+h1, +t}:
                  match t:
                    case SNil{}:
                      hy
                    case SCon{+h2, +t2}:
                      false.elim(T(isle(lo, code(h1), hi)), hy)
        case Cat{+a, +b}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.cat.w(c, p, a, b, q, cat.elim(1n+B0(c), cg(c), a, b, q, "", hy), +s1 => +s2 => +e => +ha => fi.ok(c, fl, a, 1n, 0n, s1, u, s2 ++ v, cat.sub.l(u, q, v, s1, s2, cS(c), h, e), ha), +s1 => +s2 => +e => +hb => fi.ok(c, fl, b, 1n, 0n, s2, u ++ s1, v, cat.sub.r(u, q, v, s1, s2, cS(c), h, e), hb))
        case Alt{+a, +b}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              or.elim(TR(c, a, q), TR(c, b, q), T(fi(fl, cg2(c), Alt{a, b}, q)), hy, +h1 => fi.alt.l(c, p, a, b, q, fi.ok(c, fl, a, 1n, 0n, q, u, v, h, h1)), +h2 => fi.alt.r(c, p, a, b, q, fi.ok(c, fl, b, 1n, 0n, q, u, v, h, h2)))
        case Ref{+n}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              fi.ref(c, p, n, q, fi.ok(c, p, lk(cg2(c), n), 1n, 0n, q, u, v, h, ref.down(c, n, q, u, v, h, hy)))

law may.nil:
  for +c: Cx
  for +r: R
  for +ch: U32
  for +h: T(fi(3n, cg2(c), r, ""))
  T(may(3n, cg2(c), r, ch))

def may.nil(c, r, ch, h):
  or.l(nul(3n, cg2(c), r), fst(3n, cg2(c), r, ch), h)

law may.con:
  for +c: Cx
  for +r: R
  for +x: Char
  for -t: String
  for +ch: U32
  for +e: T(U32.is_eq(ch, code(x)))
  for +h: T(fi(3n, cg2(c), r, SCon{x, t}))
  T(may(3n, cg2(c), r, ch))

def may.con(c, r, x, t, ch, e, h):
  %u32.eq.t(code(x), ch, u32.eq.sym(ch, code(x), e)) : T(may(3n, cg2(c), r, _))
  or.r(nul(3n, cg2(c), r), fst(3n, cg2(c), r, code(x)), h)
# ---- what the validator checks ----

def uB(+c: Cx) -> B:
  B{unshadow(Op, cO(c)), unshadow(U32, cA(c))}

def allow(+c: Cx, kd: Kd, +id: U32, +k: U32) -> Bool:
  match kd:
    case KBit{}:
      U32.is_eq(rdA(c, ((id + 1 : U32) + k : U32)), 1)
    case KL{}:
      al.l(rdO(c, ((id + 1 : U32) + k : U32)))
    case KR{}:
      al.r(rdO(c, ((id + 1 : U32) + k : U32)))

def pr(+c: Cx, p: P, +k: U32) -> Bool:
  match p:
    case PCls{+r, +tb}:
      bi(U32.is_eq(rdA(c, (tb + k : U32)), 1), cmatch(r, k))
    case POne{+id}:
      U32.is_eq(rdA(c, ((id + 1 : U32) + k : U32)), 1)
    case PRg{+kd, +id, +x, +y}:
      imp.b(isle(x, k, y), allow(c, kd, id, k))
    case PAll{+kd, +id}:
      allow(c, kd, id, k)

def all128(+c: Cx, +p: P, n: Nat, +k: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(pr(c, p, k), all128(c, p, m, (k + 1 : U32)))

def rngp(+c: Cx, l: LP, n: Nat, +j: U32) -> Bool:
  match l:
    case LNil{}:
      U32.is_gt(rdA(c, j), rdA(c, (j + 1 : U32)))
    case LCon{+x, +y, t}:
      match n:
        case 0n:
          False{}
        case 1n+m:
          Bool.and(Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), rngp(c, t, m, (j + 2 : U32)))

def clso(+c: Cx, +r: R, +tb: U32) -> Bool:
  Bool.and(Bool.and(leafy(r), Bool.not(cmatch(r, 4294967295))), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))))

def ckf(+c: Cx, +kd: Kd, +fl: Nat, r: R, +id: U32) -> Bool:
  match fl:
    case 0n:
      all128(c, PAll{kd, id}, 128n, 0)
    case 1n+p:
      match r:
        case Emp{}:
          True{}
        case Bad{}:
          True{}
        case Lit{+x}:
          imp.b(Bool.not(U32.is_ge(Char.to_u32(x), 128)), allow(c, kd, id, Char.to_u32(x)))
        case Rng{+x, +y}:
          all128(c, PRg{kd, id, x, y}, 128n, 0)
        case Cat{+a1, +b1}:
          Bool.and(ckf(c, kd, fl, a1, id), imp.b(nul(fl, cg2(c), a1), ckf(c, kd, fl, b1, id)))
        case Alt{+a1, +b1}:
          Bool.and(ckf(c, kd, fl, a1, id), ckf(c, kd, fl, b1, id))
        case Star{+x}:
          ckf(c, kd, fl, x, id)
        case Ref{+n}:
          ckf(c, kd, p, lk(cg2(c), n), id)

def ckm(+c: Cx, +kd: Kd, +y: R, +id: U32) -> Bool:
  Bool.and(imp.b(nul(3n, cg2(c), y), all128(c, PAll{kd, id}, 128n, 0)), ckf(c, kd, 3n, y, id))

def nok.at(+c: Cx, r: R, q: Op, +x: U32, +id: U32) -> Bool:
  match r:
    case Emp{}:
      is.oemp(q)
    case Bad{}:
      is.obad(q)
    case Lit{+h}:
      Bool.and(is.olit(q), Bool.and(U32.is_eq(x, Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295))))
    case Rng{+lo, +hi}:
      Bool.and(is.ocls(q), clso(c, Rng{lo, hi}, x))
    case Cat{a1, +y}:
      match a1:
        case Star{+z}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Star{z}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case OCatS{}:
              Bool.and(nok.at(c, z, rdO(c, low(x)), rdA(c, low(x)), low(x)), Bool.and(nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id)))
            case OCatSC{}:
              Bool.and(clso(c, z, low(x)), Bool.and(nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id)))
            case _:
              False{}
        case Emp{}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Emp{}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Bad{}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Bad{}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Lit{+c0}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Lit{c0}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Rng{+p0, +p1}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Rng{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Cat{+p0, +p1}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Cat{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Alt{+p0, +p1}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Alt{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
        case Ref{+p0}:
          match q:
            case OCat{}:
              Bool.and(nok.at(c, Ref{p0}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)))
            case _:
              False{}
    case Alt{+a1, +b2}:
      match q:
        case OCls{}:
          clso(c, Alt{a1, b2}, x)
        case OAlt{}:
          Bool.and(nok.at(c, a1, rdO(c, low(x)), rdA(c, low(x)), low(x)), Bool.and(nok.at(c, b2, rdO(c, high(x)), rdA(c, high(x)), high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))))
        case _:
          False{}
    case Star{+a1}:
      match q:
        case OStar{}:
          Bool.and(nok.at(c, a1, rdO(c, x), rdA(c, x), x), all128(c, POne{id}, 128n, 0))
        case OStarC{}:
          Bool.and(clso(c, a1, x), all128(c, POne{id}, 128n, 0))
        case _:
          False{}
    case Ref{+n}:
      match q:
        case ORefM{}:
          ref.go(crt(c), n, high(x), low(x))
        case ORef{}:
          ref.go(crt(c), n, high(x), low(x))
        case OBad{}:
          badr(lk(cg2(c), n))
        case _:
          False{}

def nok(+c: Cx, +r: R, +id: U32) -> Bool:
  nok.at(c, r, rdO(c, id), rdA(c, id), id)

def rulesp(+c: Cx, l: RT) -> Bool:
  match l:
    case RNil{}:
      True{}
    case RCon{+k, +x, t}:
      Bool.and(nok.at(c, body(cg2(c), k), rdO(c, x), rdA(c, x), x), rulesp(c, t))

def textp(+c: Cx, s: String, +i: U32, +end: U32, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), 4294967295), U32.is_eq(i, end)))
    case SCon{+h, t}:
      textp(c, t, (i + 1 : U32), end, Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)))))

def vals(+c: Cx, +r: R, +root: U32, +s: String, +st0: U32, +end: U32) -> Bool:
  Bool.and(rulesp(c, crt(c)), Bool.and(nok.at(c, r, rdO(c, root), rdA(c, root), root), textp(c, s, st0, end, True{})))

# ---- the validator computes what it says ----

law get.u:
  for +c: Cx
  for +i: U32
  {(unshadow(U32, cA(c)), rdA(c, i)) == Array.get(U32, unshadow(U32, cA(c)), i) : Array<U32> & U32}

def get.u(c, i):
  get.same(U32, cA(c), i)

law get.o:
  for +c: Cx
  for +i: U32
  {(unshadow(Op, cO(c)), rdO(c, i)) == Array.get(Op, unshadow(Op, cO(c)), i) : Array<Op> & Op}

def get.o(c, i):
  get.same(Op, cO(c), i)

law rdu.ok:
  for +c: Cx
  for +i: U32
  for -k: B -> U32 -> B & Bool
  {rdu(uB(c), i, k) == k(uB(c), rdA(c, i)) : B & Bool}

def rdu.ok(c, i, k):
  %get.u(c, i) : {rd.u2(unshadow(Op, cO(c)), k, _) == k(uB(c), rdA(c, i)) : B & Bool}
  {==}

law rdo.ok:
  for +c: Cx
  for +i: U32
  for -k: B -> Op -> B & Bool
  {rdo(uB(c), i, k) == k(uB(c), rdO(c, i)) : B & Bool}

def rdo.ok(c, i, k):
  %get.o(c, i) : {rd.o2(unshadow(U32, cA(c)), k, _) == k(uB(c), rdO(c, i)) : B & Bool}
  {==}

law with.ok:
  for +c: Cx
  for +i: U32
  for -k: B -> Op -> U32 -> B & Bool
  {with(uB(c), i, k) == k(uB(c), rdO(c, i), rdA(c, i)) : B & Bool}

def with.ok(c, i, k):
  Equal.trans(B & Bool, rdo(uB(c), i, b1 => q => rdu(b1, i, b2 => x => k(b2, q, x))), rdu(uB(c), i, b2 => x => k(b2, rdO(c, i), x)), k(uB(c), rdO(c, i), rdA(c, i)), rdo.ok(c, i, b1 => q => rdu(b1, i, b2 => x => k(b2, q, x))), rdu.ok(c, i, b2 => x => k(b2, rdO(c, i), x)))

law and.l2:
  for +c: Cx
  for p: B & Bool
  for -k: B -> B & Bool
  for v: Bool
  for -w: Bool
  for +ep: {p == (uB(c), v) : B & Bool}
  for +ek: {k(uB(c)) == (uB(c), w) : B & Bool}
  {and.k(p, k) == (uB(c), Bool.and(v, w)) : B & Bool}

law and.lv:
  for +c: Cx
  for v: Bool
  for -k: B -> B & Bool
  for -w: Bool
  for +ek: {k(uB(c)) == (uB(c), w) : B & Bool}
  {and.k((uB(c), v), k) == (uB(c), Bool.and(v, w)) : B & Bool}

def and.lv(c, v, k, w, ek):
  match v:
    case False{}:
      {==}
    case True{}:
      ek

def and.l2(c, p, k, v, w, ep, ek):
  %Equal.sym(B & Bool, p, (uB(c), v), ep) : {and.k(_, k) == (uB(c), Bool.and(v, w)) : B & Bool}
  and.lv(c, v, k, w, ek)

law imp.lv:
  for +c: Cx
  for v: Bool
  for -k: B -> B & Bool
  for -w: Bool
  for +ek: {k(uB(c)) == (uB(c), w) : B & Bool}
  {imp.k(v, uB(c), k) == (uB(c), imp.b(v, w)) : B & Bool}

def imp.lv(c, v, k, w, ek):
  match v:
    case False{}:
      {==}
    case True{}:
      ek

law allow.ok:
  for +c: Cx
  for kd: Kd
  for +id: U32
  for +k: U32
  {allow.l(kd, id, k, uB(c)) == (uB(c), allow(c, kd, id, k)) : B & Bool}

def allow.ok(c, kd, id, k):
  match kd:
    case KBit{}:
      rdu.ok(c, ((id + 1 : U32) + k : U32), b1 => +x => (b1, U32.is_eq(x, 1)))
    case KL{}:
      rdo.ok(c, ((id + 1 : U32) + k : U32), b1 => q => (b1, al.l(q)))
    case KR{}:
      rdo.ok(c, ((id + 1 : U32) + k : U32), b1 => q => (b1, al.r(q)))

law pr.ok:
  for +c: Cx
  for p: P
  for +k: U32
  {pr.l(p, k, uB(c)) == (uB(c), pr(c, p, k)) : B & Bool}

def pr.ok(c, p, k):
  match p:
    case PCls{+r, +tb}:
      rdu.ok(c, (tb + k : U32), b1 => +x => (b1, bi(U32.is_eq(x, 1), cmatch(r, k))))
    case POne{+id}:
      rdu.ok(c, ((id + 1 : U32) + k : U32), b1 => +x => (b1, U32.is_eq(x, 1)))
    case PRg{+kd, +id, +x, +y}:
      imp.lv(c, isle(x, k, y), b1 => allow.l(kd, id, k, b1), allow(c, kd, id, k), allow.ok(c, kd, id, k))
    case PAll{+kd, +id}:
      allow.ok(c, kd, id, k)

law all.ok:
  for +c: Cx
  for +p: P
  for n: Nat
  for +k: U32
  {all.l(p, n, k, uB(c)) == (uB(c), all128(c, p, n, k)) : B & Bool}

def all.ok(c, p, n, k):
  match n:
    case 0n:
      {==}
    case 1n+m:
      and.l2(c, pr.l(p, k, uB(c)), b1 => all.l(p, m, (k + 1 : U32), b1), pr(c, p, k), all128(c, p, m, (k + 1 : U32)), pr.ok(c, p, k), all.ok(c, p, m, (k + 1 : U32)))

law rng.ok:
  for +c: Cx
  for l: LP
  for +n: Nat
  for +j: U32
  {rng.l(l, n, j, uB(c)) == (uB(c), rngp(c, l, n, j)) : B & Bool}

law rd2.ok:
  for +c: Cx
  for +j: U32
  for -k: B -> U32 -> U32 -> B & Bool
  {rdu(uB(c), j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => k(b2, lo, hi))) == k(uB(c), rdA(c, j), rdA(c, (j + 1 : U32))) : B & Bool}

def rd2.ok(c, j, k):
  Equal.trans(B & Bool, rdu(uB(c), j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => k(b2, lo, hi))), rdu(uB(c), (j + 1 : U32), b2 => +hi => k(b2, rdA(c, j), hi)), k(uB(c), rdA(c, j), rdA(c, (j + 1 : U32))), rdu.ok(c, j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => k(b2, lo, hi))), rdu.ok(c, (j + 1 : U32), b2 => +hi => k(b2, rdA(c, j), hi)))

def rng.ok(c, l, n, j):
  match l:
    case LNil{}:
      rd2.ok(c, j, b2 => +lo => +hi => (b2, U32.is_gt(lo, hi)))
    case LCon{+x, +y, +t}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Equal.trans(B & Bool, rdu(uB(c), j, b1 => +lo => rdu(b1, (j + 1 : U32), b2 => +hi => and.k((b2, Bool.and(Bool.and(U32.is_eq(lo, x), U32.is_eq(hi, y)), Bool.not(U32.is_gt(x, y)))), b3 => rng.l(t, m, (j + 2 : U32), b3)))), and.k((uB(c), Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y)))), b3 => rng.l(t, m, (j + 2 : U32), b3)), (uB(c), rngp(c, LCon{x, y, t}, 1n+m, j)), rd2.ok(c, j, b2 => +lo => +hi => and.k((b2, Bool.and(Bool.and(U32.is_eq(lo, x), U32.is_eq(hi, y)), Bool.not(U32.is_gt(x, y)))), b3 => rng.l(t, m, (j + 2 : U32), b3))), and.lv(c, Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), b3 => rng.l(t, m, (j + 2 : U32), b3), rngp(c, t, m, (j + 2 : U32)), rng.ok(c, t, m, (j + 2 : U32))))

law cls.ok:
  for +c: Cx
  for +r: R
  for +tb: U32
  {cls.l(r, tb, uB(c)) == (uB(c), clso(c, r, tb)) : B & Bool}

def cls.ok(c, r, tb):
  and.lv(c, Bool.and(leafy(r), Bool.not(cmatch(r, 4294967295))), b1 => and.k(all.l(PCls{r, tb}, 128n, 0, b1), b2 => rng.l(lv(r, LNil{}), 64n, (tb + 128 : U32), b2)), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))), and.l2(c, all.l(PCls{r, tb}, 128n, 0, uB(c)), b2 => rng.l(lv(r, LNil{}), 64n, (tb + 128 : U32), b2), all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32)), all.ok(c, PCls{r, tb}, 128n, 0), rng.ok(c, lv(r, LNil{}), 64n, (tb + 128 : U32))))

law ck.fst.ok:
  for +c: Cx
  for +kd: Kd
  for +fl: Nat
  for +r: R
  for +id: U32
  {ck.fst(kd, fl, cg2(c), r, id, uB(c)) == (uB(c), ckf(c, kd, fl, r, id)) : B & Bool}

def ck.fst.ok(c, kd, fl, r, id):
  match fl:
    case 0n:
      all.ok(c, PAll{kd, id}, 128n, 0)
    case 1n+p:
      match r:
        case Emp{}:
          {==}
        case Bad{}:
          {==}
        case Lit{+x}:
          imp.lv(c, Bool.not(U32.is_ge(Char.to_u32(x), 128)), b1 => allow.l(kd, id, Char.to_u32(x), b1), allow(c, kd, id, Char.to_u32(x)), allow.ok(c, kd, id, Char.to_u32(x)))
        case Rng{+x, +y}:
          all.ok(c, PRg{kd, id, x, y}, 128n, 0)
        case Cat{+a1, +b1}:
          and.l2(c, ck.fst(kd, fl, cg2(c), a1, id, uB(c)), b2 => imp.k(nul(fl, cg2(c), a1), b2, b3 => ck.fst(kd, fl, cg2(c), b1, id, b3)), ckf(c, kd, fl, a1, id), imp.b(nul(fl, cg2(c), a1), ckf(c, kd, fl, b1, id)), ck.fst.ok(c, kd, fl, a1, id), imp.lv(c, nul(fl, cg2(c), a1), b3 => ck.fst(kd, fl, cg2(c), b1, id, b3), ckf(c, kd, fl, b1, id), ck.fst.ok(c, kd, fl, b1, id)))
        case Alt{+a1, +b1}:
          and.l2(c, ck.fst(kd, fl, cg2(c), a1, id, uB(c)), b2 => ck.fst(kd, fl, cg2(c), b1, id, b2), ckf(c, kd, fl, a1, id), ckf(c, kd, fl, b1, id), ck.fst.ok(c, kd, fl, a1, id), ck.fst.ok(c, kd, fl, b1, id))
        case Star{+x}:
          ck.fst.ok(c, kd, fl, x, id)
        case Ref{+n}:
          ck.fst.ok(c, kd, p, lk(cg2(c), n), id)

law ck.may.ok:
  for +c: Cx
  for +kd: Kd
  for +y: R
  for +id: U32
  {ck.may(kd, cg2(c), y, id, uB(c)) == (uB(c), ckm(c, kd, y, id)) : B & Bool}

def ck.may.ok(c, kd, y, id):
  and.l2(c, imp.k(nul(3n, cg2(c), y), uB(c), b1 => all.l(PAll{kd, id}, 128n, 0, b1)), b2 => ck.fst(kd, 3n, cg2(c), y, id, b2), imp.b(nul(3n, cg2(c), y), all128(c, PAll{kd, id}, 128n, 0)), ckf(c, kd, 3n, y, id), imp.lv(c, nul(3n, cg2(c), y), b1 => all.l(PAll{kd, id}, 128n, 0, b1), all128(c, PAll{kd, id}, 128n, 0), all.ok(c, PAll{kd, id}, 128n, 0)), ck.fst.ok(c, kd, 3n, y, id))

law chk.ok:
  for +c: Cx
  for +r: R
  for q: Op
  for +x: U32
  for +id: U32
  {chk.at(cg2(c), crt(c), r, q, x, id, uB(c)) == (uB(c), nok.at(c, r, q, x, id)) : B & Bool}

def chk.ok(c, r, q, x, id):
  match r:
    case Emp{}:
      {==}
    case Bad{}:
      {==}
    case Lit{+h}:
      {==}
    case Rng{+lo, +hi}:
      and.lv(c, is.ocls(q), b1 => cls.l(Rng{lo, hi}, x, b1), clso(c, Rng{lo, hi}, x), cls.ok(c, Rng{lo, hi}, x))
    case Cat{+a1, +y}:
      match a1:
        case Star{+z}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Star{z}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Star{z}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Star{z}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Star{z}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Star{z}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Star{z}, q9, x9, low(x), b9)), chk.ok(c, Star{z}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OCatS{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), z, q9, x9, low(x), b9)), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, cg2(c), y, id, b2)), nok.at(c, z, rdO(c, low(x)), rdA(c, low(x)), low(x)), Bool.and(nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), z, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), z, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, z, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), z, q9, x9, low(x), b9)), chk.ok(c, z, rdO(c, low(x)), rdA(c, low(x)), low(x))), and.l2(c, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, cg2(c), y, id, b2), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), ck.may.ok(c, KBit{}, y, id)))
            case OCatSC{}:
              and.l2(c, cls.l(z, low(x), uB(c)), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, cg2(c), y, id, b2)), clso(c, z, low(x)), Bool.and(nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id)), cls.ok(c, z, low(x)), and.l2(c, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), b2 => ck.may(KBit{}, cg2(c), y, id, b2), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), ckm(c, KBit{}, y, id), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), ck.may.ok(c, KBit{}, y, id)))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Emp{}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Emp{}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Emp{}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Emp{}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Emp{}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Emp{}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Emp{}, q9, x9, low(x), b9)), chk.ok(c, Emp{}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Bad{}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Bad{}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Bad{}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Bad{}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Bad{}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Bad{}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Bad{}, q9, x9, low(x), b9)), chk.ok(c, Bad{}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Lit{+c0}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Lit{c0}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Lit{c0}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Lit{c0}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Lit{c0}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Lit{c0}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Lit{c0}, q9, x9, low(x), b9)), chk.ok(c, Lit{c0}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Rng{+p0, +p1}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Rng{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Rng{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Rng{p0, p1}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Rng{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Rng{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Rng{p0, p1}, q9, x9, low(x), b9)), chk.ok(c, Rng{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Cat{+p0, +p1}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Cat{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Cat{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Cat{p0, p1}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Cat{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Cat{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Cat{p0, p1}, q9, x9, low(x), b9)), chk.ok(c, Cat{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Alt{+p0, +p1}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Alt{p0, p1}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Alt{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Alt{p0, p1}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Alt{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Alt{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Alt{p0, p1}, q9, x9, low(x), b9)), chk.ok(c, Alt{p0, p1}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
        case Ref{+p0}:
          match q:
            case OCat{}:
              and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Ref{p0}, q9, x9, low(x), b9)), b1 => with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), nok.at(c, Ref{p0}, rdO(c, low(x)), rdA(c, low(x)), low(x)), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x)), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Ref{p0}, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), Ref{p0}, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, Ref{p0}, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), Ref{p0}, q9, x9, low(x), b9)), chk.ok(c, Ref{p0}, rdO(c, low(x)), rdA(c, low(x)), low(x))), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), y, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), y, q9, x9, high(x), b9)), chk.ok(c, y, rdO(c, high(x)), rdA(c, high(x)), high(x))))
            case OLit{}:
              {==}
            case OCls{}:
              {==}
            case OAlt{}:
              {==}
            case OCatS{}:
              {==}
            case OCatSC{}:
              {==}
            case OStar{}:
              {==}
            case OStarC{}:
              {==}
            case ORefM{}:
              {==}
            case ORef{}:
              {==}
            case OEmp{}:
              {==}
            case OBad{}:
              {==}
            case ASelB{}:
              {==}
            case ASelL{}:
              {==}
            case ASelR{}:
              {==}
            case ASelN{}:
              {==}
    case Alt{+a1, +b2}:
      match q:
        case OCls{}:
          cls.ok(c, Alt{a1, b2}, x)
        case OAlt{}:
          and.l2(c, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, low(x), b9)), b1 => and.k(with(b1, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), b2, q9, x9, high(x), b9)), b3 => and.k(ck.may(KL{}, cg2(c), a1, id, b3), b5 => ck.may(KR{}, cg2(c), b2, id, b5))), nok.at(c, a1, rdO(c, low(x)), rdA(c, low(x)), low(x)), Bool.and(nok.at(c, b2, rdO(c, high(x)), rdA(c, high(x)), high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))), Equal.trans(B & Bool, with(uB(c), low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, low(x), b9)), chk.at(cg2(c), crt(c), a1, rdO(c, low(x)), rdA(c, low(x)), low(x), uB(c)), (uB(c), nok.at(c, a1, rdO(c, low(x)), rdA(c, low(x)), low(x))), with.ok(c, low(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, low(x), b9)), chk.ok(c, a1, rdO(c, low(x)), rdA(c, low(x)), low(x))), and.l2(c, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), b2, q9, x9, high(x), b9)), b3 => and.k(ck.may(KL{}, cg2(c), a1, id, b3), b5 => ck.may(KR{}, cg2(c), b2, id, b5)), nok.at(c, b2, rdO(c, high(x)), rdA(c, high(x)), high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id)), Equal.trans(B & Bool, with(uB(c), high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), b2, q9, x9, high(x), b9)), chk.at(cg2(c), crt(c), b2, rdO(c, high(x)), rdA(c, high(x)), high(x), uB(c)), (uB(c), nok.at(c, b2, rdO(c, high(x)), rdA(c, high(x)), high(x))), with.ok(c, high(x), b9 => q9 => +x9 => chk.at(cg2(c), crt(c), b2, q9, x9, high(x), b9)), chk.ok(c, b2, rdO(c, high(x)), rdA(c, high(x)), high(x))), and.l2(c, ck.may(KL{}, cg2(c), a1, id, uB(c)), b5 => ck.may(KR{}, cg2(c), b2, id, b5), ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id), ck.may.ok(c, KL{}, a1, id), ck.may.ok(c, KR{}, b2, id))))
        case OLit{}:
          {==}
        case OCat{}:
          {==}
        case OCatS{}:
          {==}
        case OCatSC{}:
          {==}
        case OStar{}:
          {==}
        case OStarC{}:
          {==}
        case ORefM{}:
          {==}
        case ORef{}:
          {==}
        case OEmp{}:
          {==}
        case OBad{}:
          {==}
        case ASelB{}:
          {==}
        case ASelL{}:
          {==}
        case ASelR{}:
          {==}
        case ASelN{}:
          {==}
    case Star{+a1}:
      match q:
        case OStar{}:
          and.l2(c, with(uB(c), x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, x, b9)), b1 => all.l(POne{id}, 128n, 0, b1), nok.at(c, a1, rdO(c, x), rdA(c, x), x), all128(c, POne{id}, 128n, 0), Equal.trans(B & Bool, with(uB(c), x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, x, b9)), chk.at(cg2(c), crt(c), a1, rdO(c, x), rdA(c, x), x, uB(c)), (uB(c), nok.at(c, a1, rdO(c, x), rdA(c, x), x)), with.ok(c, x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), a1, q9, x9, x, b9)), chk.ok(c, a1, rdO(c, x), rdA(c, x), x)), all.ok(c, POne{id}, 128n, 0))
        case OStarC{}:
          and.l2(c, cls.l(a1, x, uB(c)), b1 => all.l(POne{id}, 128n, 0, b1), clso(c, a1, x), all128(c, POne{id}, 128n, 0), cls.ok(c, a1, x), all.ok(c, POne{id}, 128n, 0))
        case OLit{}:
          {==}
        case OCls{}:
          {==}
        case OAlt{}:
          {==}
        case OCat{}:
          {==}
        case OCatS{}:
          {==}
        case OCatSC{}:
          {==}
        case ORefM{}:
          {==}
        case ORef{}:
          {==}
        case OEmp{}:
          {==}
        case OBad{}:
          {==}
        case ASelB{}:
          {==}
        case ASelL{}:
          {==}
        case ASelR{}:
          {==}
        case ASelN{}:
          {==}
    case Ref{+n}:
      match q:
        case OLit{}:
          {==}
        case OCls{}:
          {==}
        case OAlt{}:
          {==}
        case OCat{}:
          {==}
        case OCatS{}:
          {==}
        case OCatSC{}:
          {==}
        case OStar{}:
          {==}
        case OStarC{}:
          {==}
        case ORefM{}:
          {==}
        case ORef{}:
          {==}
        case OEmp{}:
          {==}
        case OBad{}:
          {==}
        case ASelB{}:
          {==}
        case ASelL{}:
          {==}
        case ASelR{}:
          {==}
        case ASelN{}:
          {==}

law rules.ok:
  for +c: Cx
  for l: RT
  {rules.l(cg2(c), crt(c), l, uB(c)) == (uB(c), rulesp(c, l)) : B & Bool}

def rules.ok(c, l):
  match l:
    case RNil{}:
      {==}
    case RCon{+k, +x, +t}:
      and.l2(c, with(uB(c), x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), body(cg2(c), k), q9, x9, x, b9)), b1 => rules.l(cg2(c), crt(c), t, b1), nok.at(c, body(cg2(c), k), rdO(c, x), rdA(c, x), x), rulesp(c, t), Equal.trans(B & Bool, with(uB(c), x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), body(cg2(c), k), q9, x9, x, b9)), chk.at(cg2(c), crt(c), body(cg2(c), k), rdO(c, x), rdA(c, x), x, uB(c)), (uB(c), nok.at(c, body(cg2(c), k), rdO(c, x), rdA(c, x), x)), with.ok(c, x, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), body(cg2(c), k), q9, x9, x, b9)), chk.ok(c, body(cg2(c), k), rdO(c, x), rdA(c, x), x)), rules.ok(c, t))

law text.a.ok:
  for +c: Cx
  for s: String
  for +i: U32
  for +end: U32
  for ok: Bool
  {text.a(s, i, end, ok, (unshadow(U32, cA(c)), rdA(c, i))) == (unshadow(U32, cA(c)), textp(c, s, i, end, ok)) : Array<U32> & Bool}

def text.a.ok(c, s, i, end, ok):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %get.u(c, (i + 1 : U32)) : {text.a(t, (i + 1 : U32), end, Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)))), _) == (unshadow(U32, cA(c)), textp(c, SCon{h, t}, i, end, ok)) : Array<U32> & Bool}
      text.a.ok(c, t, (i + 1 : U32), end, Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)))))

law text.ok:
  for +c: Cx
  for +s: String
  for +i: U32
  for +end: U32
  {text.l(s, i, end, uB(c)) == (uB(c), textp(c, s, i, end, True{})) : B & Bool}

def text.ok(c, s, i, end):
  %get.u(c, i) : {text.fin(unshadow(Op, cO(c)), text.a(s, i, end, True{}, _)) == (uB(c), textp(c, s, i, end, True{})) : B & Bool}
  %Equal.sym(Array<U32> & Bool, text.a(s, i, end, True{}, (unshadow(U32, cA(c)), rdA(c, i))), (unshadow(U32, cA(c)), textp(c, s, i, end, True{})), text.a.ok(c, s, i, end, True{})) : {text.fin(unshadow(Op, cO(c)), _) == (uB(c), textp(c, s, i, end, True{})) : B & Bool}
  {==}

law val.ok:
  for +c: Cx
  for +r: R
  for +root: U32
  for +s: String
  for +st0: U32
  for +end: U32
  {validate(cg2(c), crt(c), r, root, s, st0, end, uB(c)) == (uB(c), vals(c, r, root, s, st0, end)) : B & Bool}

def val.ok(c, r, root, s, st0, end):
  and.l2(c, rules.l(cg2(c), crt(c), crt(c), uB(c)), b1 => and.k(with(b1, root, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), r, q9, x9, root, b9)), b2 => text.l(s, st0, end, b2)), rulesp(c, crt(c)), Bool.and(nok.at(c, r, rdO(c, root), rdA(c, root), root), textp(c, s, st0, end, True{})), rules.ok(c, crt(c)), and.l2(c, with(uB(c), root, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), r, q9, x9, root, b9)), b2 => text.l(s, st0, end, b2), nok.at(c, r, rdO(c, root), rdA(c, root), root), textp(c, s, st0, end, True{}), Equal.trans(B & Bool, with(uB(c), root, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), r, q9, x9, root, b9)), chk.at(cg2(c), crt(c), r, rdO(c, root), rdA(c, root), root, uB(c)), (uB(c), nok.at(c, r, rdO(c, root), rdA(c, root), root)), with.ok(c, root, b9 => q9 => +x9 => chk.at(cg2(c), crt(c), r, q9, x9, root, b9)), chk.ok(c, r, rdO(c, root), rdA(c, root), root)), text.ok(c, s, st0, end)))
# ---- reading the tables ----

def uA(+c: Cx) -> Array<U32>:
  unshadow(U32, cA(c))

def uO(+c: Cx) -> Array<Op>:
  unshadow(Op, cO(c))

law le.ne.succ:
  for +a: Nat
  for +b: Nat
  for +h: T(Nat.is_le(a, b))
  for +he: {Nat.is_eq(a, b) == False{} : Bool}
  T(Nat.is_le(1n+a, b))

def le.ne.succ(a, b, h, he):
  match a b:
    case 0n 0n:
      absurd(T(Nat.is_le(1n, 0n)), true.not_false(he))
    case 0n 1n+q:
      le0(q)
    case 1n+p 0n:
      false.elim(T(Nat.is_le(2n+p, 0n)), h)
    case 1n+p 1n+q:
      le.ne.succ(p, q, h, he)

law no.lt:
  for a: Nat
  for b: Nat
  for +h1: T(Nat.is_le(a, b))
  for +h2: T(Nat.is_le(1n+b, a))
  Empty

def no.lt(a, b, h1, h2):
  match a b:
    case 0n 0n:
      false.empty(h2)
    case 0n 1n+q:
      false.empty(h2)
    case 1n+p 0n:
      false.empty(h1)
    case 1n+p 1n+q:
      no.lt(p, q, h1, h2)

law cmp.lt.le:
  for a: Nat
  for b: Nat
  for +h: {Nat.cmp(a, b) == LT{} : Cmp}
  T(Nat.is_le(1n+a, b))

def cmp.lt.le(a, b, h):
  match a b:
    case 0n 0n:
      absurd(T(Nat.is_le(1n, 0n)), eq.not.lt(h))
    case 0n 1n+q:
      le0(q)
    case 1n+p 0n:
      absurd(T(Nat.is_le(2n+p, 0n)), gt.not.lt(h))
    case 1n+p 1n+q:
      cmp.lt.le(p, q, h)

law ge.f.lt:
  for c: Cmp
  for +h: {Cmp.is_ge(c) == False{} : Bool}
  {c == LT{} : Cmp}

def ge.f.lt(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      absurd({EQ{} == LT{} : Cmp}, true.not_false(h))
    case GT{}:
      absurd({GT{} == LT{} : Cmp}, true.not_false(h))

law lt128:
  for +ch: U32
  for +h: {U32.is_ge(ch, 128) == False{} : Bool}
  T(Nat.is_le(1n+N(ch), 128n))

def lt128(ch, h):
  cmp.lt.le(N(ch), 128n, Equal.trans(Cmp, Nat.cmp(N(ch), 128n), U32.cmp(ch, 128), LT{}, u32.cmp.nat(ch, 128), ge.f.lt(U32.cmp(ch, 128), h)))

law tr.pr:
  for +c: Cx
  for +p: P
  for +k: U32
  for +ch: U32
  for +e: T(U32.is_eq(k, ch))
  for +h: T(pr(c, p, k))
  T(pr(c, p, ch))

def tr.pr(c, p, k, ch, e, h):
  %u32.eq.t(k, ch, e) : T(pr(c, p, _))
  h

law hl.step:
  for +k: U32
  for +ch: U32
  for +hl: T(Nat.is_le(N(k), N(ch)))
  for +ne: {U32.is_eq(k, ch) == False{} : Bool}
  T(Nat.is_le(1n+N(k), N(ch)))

def hl.step(k, ch, hl, ne):
  le.ne.succ(N(k), N(ch), hl, Equal.trans(Bool, Nat.is_eq(N(k), N(ch)), U32.is_eq(k, ch), False{}, u32.eq.nat(k, ch), ne))

law hl.step2:
  for +k: U32
  for +ch: U32
  for +h1: T(Nat.is_le(1n+N(k), N(ch)))
  T(Nat.is_le(N(U32.add(k, 1)), N(ch)))

def hl.step2(k, ch, h1):
  %u32.succ.nat(k, ch, h1) : T(Nat.is_le(_, N(ch)))
  h1

law hu.step:
  for +k: U32
  for +ch: U32
  for +m: Nat
  for +h1: T(Nat.is_le(1n+N(k), N(ch)))
  for +hu: T(Nat.is_le(1n+N(ch), 1n+Nat.add(m, N(k))))
  T(Nat.is_le(1n+N(ch), Nat.add(m, N(U32.add(k, 1)))))

def hu.step(k, ch, m, h1, hu):
  %u32.succ.nat(k, ch, h1) : T(Nat.is_le(1n+N(ch), Nat.add(m, _)))
  %add.succ(m, N(k)) : T(Nat.is_le(1n+N(ch), _))
  hu

law all.ex:
  for +n: Nat
  for +c: Cx
  for +p: P
  for +k: U32
  for +ch: U32
  for +h: T(all128(c, p, n, k))
  for +hl: T(Nat.is_le(N(k), N(ch)))
  for +hu: T(Nat.is_le(1n+N(ch), Nat.add(n, N(k))))
  T(pr(c, p, ch))

def all.ex(n, c, p, k, ch, h, hl, hu):
  match n:
    case 0n:
      absurd(T(pr(c, p, ch)), no.lt(N(k), N(ch), hl, hu))
    case 1n+m:
      bool.split(U32.is_eq(k, ch), T(pr(c, p, ch)), +e => tr.pr(c, p, k, ch, e, and.l(pr(c, p, k), all128(c, p, m, (k + 1 : U32)), h)), +ne => all.ex(m, c, p, (k + 1 : U32), ch, and.r(pr(c, p, k), all128(c, p, m, (k + 1 : U32)), h), hl.step2(k, ch, hl.step(k, ch, hl, ne)), hu.step(k, ch, m, hl.step(k, ch, hl, ne), hu)))

law all.at:
  for +c: Cx
  for +p: P
  for +ch: U32
  for +h: T(all128(c, p, 128n, 0))
  for +hb: {U32.is_ge(ch, 128) == False{} : Bool}
  T(pr(c, p, ch))

def all.at(c, p, ch, h, hb):
  all.ex(128n, c, p, 0, ch, h, le0(N(ch)), lt128(ch, hb))

# ---- character classes ----

def anyl(l: LP, +ch: U32) -> Bool:
  match l:
    case LNil{}:
      False{}
    case LCon{+x, +y, t}:
      Bool.or(isle(x, ch, y), anyl(t, ch))

law inr.rd:
  for +c: Cx
  for +j: U32
  for -k: Array<U32> -> U32 -> U32 -> (Array<U32> & Bool)
  {inr.b(Array.get(U32, uA(c), j), a1 => +lo => inr.b(Array.get(U32, a1, (j + 1 : U32)), a2 => +hi => k(a2, lo, hi))) == k(uA(c), rdA(c, j), rdA(c, (j + 1 : U32))) : Array<U32> & Bool}

def inr.rd(c, j, k):
  %get.u(c, j) : {inr.b(_, a1 => +lo => inr.b(Array.get(U32, a1, (j + 1 : U32)), a2 => +hi => k(a2, lo, hi))) == k(uA(c), rdA(c, j), rdA(c, (j + 1 : U32))) : Array<U32> & Bool}
  %get.u(c, (j + 1 : U32)) : {inr.b(_, a2 => +hi => k(a2, rdA(c, j), hi)) == k(uA(c), rdA(c, j), rdA(c, (j + 1 : U32))) : Array<U32> & Bool}
  {==}

law inr.d.stop:
  for stop: Bool
  for -hit: Bool
  for -a: Array<U32>
  for -k: Array<U32> -> (Array<U32> & Bool)
  for +e: {stop == True{} : Bool}
  {inr.d(stop, hit, a, k) == (a, False{}) : Array<U32> & Bool}

def inr.d.stop(stop, hit, a, k, e):
  match stop:
    case True{}:
      {==}
    case False{}:
      absurd({inr.d(False{}, hit, a, k) == (a, False{}) : Array<U32> & Bool}, false.empty(e))

law inr.d.go:
  for hit: Bool
  for +c: Cx
  for -k: Array<U32> -> (Array<U32> & Bool)
  for -rest: Bool
  for +ih: {k(uA(c)) == (uA(c), rest) : Array<U32> & Bool}
  {inr.d(False{}, hit, uA(c), k) == (uA(c), Bool.or(hit, rest)) : Array<U32> & Bool}

def inr.d.go(hit, c, k, rest, ih):
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

law gt.lit:
  for +x: U32
  for +y: U32
  for +h: T(Bool.not(U32.is_gt(x, y)))
  {U32.is_gt(x, y) == False{} : Bool}

def gt.lit(x, y, h):
  not.f(U32.is_gt(x, y), h)

law inr.ok:
  for l: LP
  for +c: Cx
  for +n: Nat
  for +j: U32
  for +ch: U32
  for +hr: T(rngp(c, l, n, j))
  {inr(n, j, ch, uA(c)) == (uA(c), anyl(l, ch)) : Array<U32> & Bool}

law inr.lcon.k:
  for +c: Cx
  for +x: U32
  for +y: U32
  for -t: LP
  for +m: Nat
  for +j: U32
  for +ch: U32
  for -rest: Bool
  for +e1: T(U32.is_eq(rdA(c, j), x))
  for +e2: T(U32.is_eq(rdA(c, (j + 1 : U32)), y))
  for +ng: T(Bool.not(U32.is_gt(x, y)))
  for +ih: {inr(m, (j + 2 : U32), ch, uA(c)) == (uA(c), rest) : Array<U32> & Bool}
  {inr.d(U32.is_gt(rdA(c, j), rdA(c, (j + 1 : U32))), isle(rdA(c, j), ch, rdA(c, (j + 1 : U32))), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)) == (uA(c), Bool.or(isle(x, ch, y), rest)) : Array<U32> & Bool}

def inr.lcon.k(c, x, y, t, m, j, ch, rest, e1, e2, ng, ih):
  %Equal.sym(U32, rdA(c, j), x, u32.eq.t(rdA(c, j), x, e1)) : {inr.d(U32.is_gt(_, rdA(c, (j + 1 : U32))), isle(_, ch, rdA(c, (j + 1 : U32))), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)) == (uA(c), Bool.or(isle(x, ch, y), rest)) : Array<U32> & Bool}
  %Equal.sym(U32, rdA(c, (j + 1 : U32)), y, u32.eq.t(rdA(c, (j + 1 : U32)), y, e2)) : {inr.d(U32.is_gt(x, _), isle(x, ch, _), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)) == (uA(c), Bool.or(isle(x, ch, y), rest)) : Array<U32> & Bool}
  %Equal.sym(Bool, U32.is_gt(x, y), False{}, gt.lit(x, y, ng)) : {inr.d(_, isle(x, ch, y), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)) == (uA(c), Bool.or(isle(x, ch, y), rest)) : Array<U32> & Bool}
  inr.d.go(isle(x, ch, y), c, a3 => inr(m, (j + 2 : U32), ch, a3), rest, ih)

def inr.ok(l, c, n, j, ch, hr):
  match l:
    case LNil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Equal.trans(Array<U32> & Bool, inr(1n+m, j, ch, uA(c)), inr.d(U32.is_gt(rdA(c, j), rdA(c, (j + 1 : U32))), isle(rdA(c, j), ch, rdA(c, (j + 1 : U32))), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)), (uA(c), False{}), inr.rd(c, j, a2 => +lo => +hi => inr.d(U32.is_gt(lo, hi), isle(lo, ch, hi), a2, a3 => inr(m, (j + 2 : U32), ch, a3))), inr.d.stop(U32.is_gt(rdA(c, j), rdA(c, (j + 1 : U32))), isle(rdA(c, j), ch, rdA(c, (j + 1 : U32))), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3), hr))
    case LCon{+x, +y, +t}:
      match n:
        case 0n:
          false.elim({inr(0n, j, ch, uA(c)) == (uA(c), anyl(LCon{x, y, t}, ch)) : Array<U32> & Bool}, hr)
        case 1n+m:
          Equal.trans(Array<U32> & Bool, inr(1n+m, j, ch, uA(c)), inr.d(U32.is_gt(rdA(c, j), rdA(c, (j + 1 : U32))), isle(rdA(c, j), ch, rdA(c, (j + 1 : U32))), uA(c), a3 => inr(m, (j + 2 : U32), ch, a3)), (uA(c), anyl(LCon{x, y, t}, ch)), inr.rd(c, j, a2 => +lo => +hi => inr.d(U32.is_gt(lo, hi), isle(lo, ch, hi), a2, a3 => inr(m, (j + 2 : U32), ch, a3))), inr.lcon.k(c, x, y, t, m, j, ch, anyl(t, ch), and.l(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y), and.l(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y)), and.l(Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), rngp(c, t, m, (j + 2 : U32)), hr))), and.r(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y), and.l(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y)), and.l(Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), rngp(c, t, m, (j + 2 : U32)), hr))), and.r(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y)), and.l(Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), rngp(c, t, m, (j + 2 : U32)), hr)), inr.ok(t, c, m, (j + 2 : U32), ch, and.r(Bool.and(Bool.and(U32.is_eq(rdA(c, j), x), U32.is_eq(rdA(c, (j + 1 : U32)), y)), Bool.not(U32.is_gt(x, y))), rngp(c, t, m, (j + 2 : U32)), hr))))

law nat.and.eq:
  for a: Nat
  for b: Nat
  {Bool.and(Nat.is_le(a, b), Nat.is_le(b, a)) == Nat.is_eq(a, b) : Bool}

def nat.and.eq(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.and.eq(p, q)

law isle.same:
  for +x: U32
  for +ch: U32
  {isle(x, ch, x) == U32.is_eq(x, ch) : Bool}

def isle.same(x, ch):
  %u32.le.nat(x, ch) : {Bool.and(_, U32.is_le(ch, x)) == U32.is_eq(x, ch) : Bool}
  %u32.le.nat(ch, x) : {Bool.and(Nat.is_le(N(x), N(ch)), _) == U32.is_eq(x, ch) : Bool}
  %u32.eq.nat(x, ch) : {Bool.and(Nat.is_le(N(x), N(ch)), Nat.is_le(N(ch), N(x))) == _ : Bool}
  nat.and.eq(N(x), N(ch))

law or.assoc:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}

def or.assoc(a, b, c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law or.tail.k:
  for a: Bool
  for -b: Bool
  for -x: Bool
  for -y: Bool
  for +e: {x == Bool.or(b, y) : Bool}
  {Bool.or(a, x) == Bool.or(Bool.or(a, b), y) : Bool}

def or.tail.k(a, b, x, y, e):
  %Equal.sym(Bool, x, Bool.or(b, y), e) : {Bool.or(a, _) == Bool.or(Bool.or(a, b), y) : Bool}
  or.assoc(a, b, y)

law cm.lv:
  for r: R
  for +acc: LP
  for +ch: U32
  {anyl(lv(r, acc), ch) == Bool.or(cmatch(r, ch), anyl(acc, ch)) : Bool}

def cm.lv(r, acc, ch):
  match r:
    case Lit{+x}:
      %isle.same(Char.to_u32(x), ch) : {Bool.or(isle(Char.to_u32(x), ch, Char.to_u32(x)), anyl(acc, ch)) == Bool.or(_, anyl(acc, ch)) : Bool}
      {==}
    case Rng{+x, +y}:
      {==}
    case Alt{+a, +b}:
      Equal.trans(Bool, anyl(lv(a, lv(b, acc)), ch), Bool.or(cmatch(a, ch), anyl(lv(b, acc), ch)), Bool.or(Bool.or(cmatch(a, ch), cmatch(b, ch)), anyl(acc, ch)), cm.lv(a, lv(b, acc), ch), or.tail.k(cmatch(a, ch), cmatch(b, ch), anyl(lv(b, acc), ch), anyl(acc, ch), cm.lv(b, acc, ch)))
    case Emp{}:
      {==}
    case Bad{}:
      {==}
    case Cat{a, b}:
      {==}
    case Star{a}:
      {==}
    case Ref{n}:
      {==}
# ---- executing single steps ----

def OO(+c: Cx, +tm: Tree<Entry>, v: V) -> Out:
  O{unshadow(Op, cO(c)), unshadow(U32, cA(c)), unshadow(Entry, tm), v}

law call.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for -v: V
  for +i: U32
  {call(OO(c, tm, v), i) == OO(c, tm, VNode{rdO(c, i), rdA(c, i)}) : Out}

def call.ok(c, tm, v, i):
  %get.o(c, i) : {call.k1(uA(c), unshadow(Entry, tm), i, _) == OO(c, tm, VNode{rdO(c, i), rdA(c, i)}) : Out}
  %get.u(c, i) : {call.k2(rdO(c, i), uO(c), unshadow(Entry, tm), _) == OO(c, tm, VNode{rdO(c, i), rdA(c, i)}) : Out}
  {==}

law clso.leafy:
  for +c: Cx
  for +r: R
  for +tb: U32
  for +h: T(clso(c, r, tb))
  T(leafy(r))

def clso.leafy(c, r, tb, h):
  and.l(leafy(r), Bool.not(cmatch(r, END)), and.l(Bool.and(leafy(r), Bool.not(cmatch(r, END))), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))), h))

law clso.nend:
  for +c: Cx
  for +r: R
  for +tb: U32
  for +h: T(clso(c, r, tb))
  T(Bool.not(cmatch(r, END)))

def clso.nend(c, r, tb, h):
  and.r(leafy(r), Bool.not(cmatch(r, END)), and.l(Bool.and(leafy(r), Bool.not(cmatch(r, END))), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))), h))

law clso.all:
  for +c: Cx
  for +r: R
  for +tb: U32
  for +h: T(clso(c, r, tb))
  T(all128(c, PCls{r, tb}, 128n, 0))

def clso.all(c, r, tb, h):
  and.l(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32)), and.r(Bool.and(leafy(r), Bool.not(cmatch(r, END))), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))), h))

law clso.rng:
  for +c: Cx
  for +r: R
  for +tb: U32
  for +h: T(clso(c, r, tb))
  T(rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32)))

def clso.rng(c, r, tb, h):
  and.r(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32)), and.r(Bool.and(leafy(r), Bool.not(cmatch(r, END))), Bool.and(all128(c, PCls{r, tb}, 128n, 0), rngp(c, lv(r, LNil{}), 64n, (tb + 128 : U32))), h))

law or.false.r:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or.false.r(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

law cm.ok:
  for +r: R
  for +ch: U32
  {anyl(lv(r, LNil{}), ch) == cmatch(r, ch) : Bool}

def cm.ok(r, ch):
  Equal.trans(Bool, anyl(lv(r, LNil{}), ch), Bool.or(cmatch(r, ch), False{}), cmatch(r, ch), cm.lv(r, LNil{}, ch), or.false.r(cmatch(r, ch)))

law cls.t.ok:
  for +c: Cx
  for big: Bool
  for +r: R
  for +tb: U32
  for +ch: U32
  for +hb: {big == U32.is_ge(ch, 128) : Bool}
  for +hv: T(clso(c, r, tb))
  {cls.t(big, uA(c), tb, ch) == (uA(c), cmatch(r, ch)) : Array<U32> & Bool}

def cls.t.ok(c, big, r, tb, ch, hb, hv):
  match big:
    case False{}:
      %get.u(c, (tb + ch : U32)) : {cls.t2(_) == (uA(c), cmatch(r, ch)) : Array<U32> & Bool}
      %Equal.sym(Bool, U32.is_eq(rdA(c, (tb + ch : U32)), 1), cmatch(r, ch), bi.eq(U32.is_eq(rdA(c, (tb + ch : U32)), 1), cmatch(r, ch), all.at(c, PCls{r, tb}, ch, clso.all(c, r, tb, hv), Equal.sym(Bool, False{}, U32.is_ge(ch, 128), hb)))) : {(uA(c), _) == (uA(c), cmatch(r, ch)) : Array<U32> & Bool}
      {==}
    case True{}:
      %cm.ok(r, ch) : {inr(64n, (tb + 128 : U32), ch, uA(c)) == (uA(c), _) : Array<U32> & Bool}
      inr.ok(lv(r, LNil{}), c, 64n, (tb + 128 : U32), ch, clso.rng(c, r, tb, hv))

law cls.do.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for +r: R
  for +tb: U32
  for +i: U32
  for +hv: T(clso(c, r, tb))
  {cls.do(tb, i, uO(c), uA(c), unshadow(Entry, tm)) == OO(c, tm, single(cmatch(r, rdA(c, i)), i)) : Out}

def cls.do.ok(c, tm, r, tb, i, hv):
  %get.u(c, i) : {cls.k1(tb, i, uO(c), unshadow(Entry, tm), _) == OO(c, tm, single(cmatch(r, rdA(c, i)), i)) : Out}
  %Equal.sym(Array<U32> & Bool, cls.t(U32.is_ge(rdA(c, i), 128), uA(c), tb, rdA(c, i)), (uA(c), cmatch(r, rdA(c, i))), cls.t.ok(c, U32.is_ge(rdA(c, i), 128), r, tb, rdA(c, i), {==}, hv)) : {cls.k2(i, uO(c), unshadow(Entry, tm), _) == OO(c, tm, single(cmatch(r, rdA(c, i)), i)) : Out}
  {==}

law lit.do.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for +x: U32
  for +i: U32
  {lit.do(x, i, uO(c), uA(c), unshadow(Entry, tm)) == OO(c, tm, single(U32.is_eq(x, rdA(c, i)), i)) : Out}

def lit.do.ok(c, tm, x, i):
  %get.u(c, i) : {lit.k(x, i, uO(c), unshadow(Entry, tm), _) == OO(c, tm, single(U32.is_eq(x, rdA(c, i)), i)) : Out}
  {==}

# alternation: the selector

def altv(+c: Cx, big: Bool, +id: U32, +ch: U32) -> V:
  match big:
    case True{}:
      VNode{ASelB{}, 0}
    case False{}:
      VNode{rdO(c, ((id + 1 : U32) + ch : U32)), 0}

law alt.pick.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for big: Bool
  for +id: U32
  for +ch: U32
  {alt.pick(big, uO(c), uA(c), unshadow(Entry, tm), id, ch) == OO(c, tm, altv(c, big, id, ch)) : Out}

def alt.pick.ok(c, tm, big, id, ch):
  match big:
    case True{}:
      {==}
    case False{}:
      %get.o(c, ((id + 1 : U32) + ch : U32)) : {alt.k2(uA(c), unshadow(Entry, tm), _) == OO(c, tm, altv(c, False{}, id, ch)) : Out}
      {==}

law alt.sel.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for +id: U32
  for +i: U32
  {alt.sel(uO(c), uA(c), unshadow(Entry, tm), id, i) == OO(c, tm, altv(c, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))) : Out}

def alt.sel.ok(c, tm, id, i):
  %get.u(c, i) : {alt.k1(uO(c), unshadow(Entry, tm), id, _) == OO(c, tm, altv(c, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))) : Out}
  alt.pick.ok(c, tm, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))

# repetition: kept or dropped

law kp.pick.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for big: Bool
  for +id: U32
  for +ch: U32
  {kp.pick(big, uO(c), uA(c), unshadow(Entry, tm), id, ch) == OO(c, tm, VNode{kp.op(kept.go(big, c, id, ch)), 0}) : Out}

def kp.pick.ok(c, tm, big, id, ch):
  match big:
    case True{}:
      {==}
    case False{}:
      %get.u(c, ((id + 1 : U32) + ch : U32)) : {kp.k3(_, uO(c), unshadow(Entry, tm)) == OO(c, tm, VNode{kp.op(kept.go(False{}, c, id, ch)), 0}) : Out}
      {==}

law kp.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for +id: U32
  for +i: U32
  {kp(uO(c), uA(c), unshadow(Entry, tm), id, i) == OO(c, tm, VNode{kp.op(kept(c, id, i)), 0}) : Out}

def kp.ok(c, tm, id, i):
  %get.u(c, i) : {kp.k1(uO(c), unshadow(Entry, tm), id, _) == OO(c, tm, VNode{kp.op(kept(c, id, i)), 0}) : Out}
  kp.pick.ok(c, tm, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))

def is.asb(q: Op) -> Bool:
  match q:
    case ASelB{}:
      True{}
    case _:
      False{}

law is.asb.op:
  for b: Bool
  {is.asb(kp.op(b)) == b : Bool}

def is.asb.op(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# step of the class scanner

law gbit.ok:
  for +c: Cx
  for big: Bool
  for +r: R
  for +tb: U32
  for +gid: U32
  for +ch: U32
  for +hv: T(clso(c, r, tb))
  {step.k2(tb, ch, gbit(big, uA(c), gid, ch)) == (uA(c), F{kept.go(big, c, gid, ch), cmatch(r, ch)}) : Array<U32> & F}

def gbit.ok(c, big, r, tb, gid, ch, hv):
  match big:
    case True{}:
      %Equal.sym(Array<U32> & Bool, cls.t(U32.is_ge(ch, 128), uA(c), tb, ch), (uA(c), cmatch(r, ch)), cls.t.ok(c, U32.is_ge(ch, 128), r, tb, ch, {==}, hv)) : {step.k3(U32.is_eq(1, 1), _) == (uA(c), F{True{}, cmatch(r, ch)}) : Array<U32> & F}
      {==}
    case False{}:
      %get.u(c, ((gid + 1 : U32) + ch : U32)) : {step.k2(tb, ch, _) == (uA(c), F{kept.go(False{}, c, gid, ch), cmatch(r, ch)}) : Array<U32> & F}
      %Equal.sym(Array<U32> & Bool, cls.t(U32.is_ge(ch, 128), uA(c), tb, ch), (uA(c), cmatch(r, ch)), cls.t.ok(c, U32.is_ge(ch, 128), r, tb, ch, {==}, hv)) : {step.k3(U32.is_eq(rdA(c, ((gid + 1 : U32) + ch : U32)), 1), _) == (uA(c), F{kept.go(False{}, c, gid, ch), cmatch(r, ch)}) : Array<U32> & F}
      {==}

law step.ok:
  for +c: Cx
  for +r: R
  for +tb: U32
  for +gid: U32
  for +i: U32
  for +hv: T(clso(c, r, tb))
  {step(uA(c), tb, gid, i) == (uA(c), F{kept(c, gid, i), cmatch(r, rdA(c, i))}) : Array<U32> & F}

def step.ok(c, r, tb, gid, i, hv):
  %get.u(c, i) : {step.k1(tb, gid, _) == (uA(c), F{kept(c, gid, i), cmatch(r, rdA(c, i))}) : Array<U32> & F}
  gbit.ok(c, U32.is_ge(rdA(c, i), 128), r, tb, gid, rdA(c, i), hv)

# memo cells

def rk(t: RT, +h: U32) -> String:
  match t:
    case RNil{}:
      ""
    case RCon{+k, +x, r}:
      ifs(U32.is_eq(h, 0), k, rk(r, (h - 1 : U32)))

def rl(+c: Cx, +w: U32) -> R:
  body(cg2(c), rk(crt(c), high(w)))

def ent.ok(+c: Cx, e: Entry) -> Bool:
  match e:
    case ENone{}:
      True{}
    case EOk{+k, +h, +l}:
      Bool.and(cell(c, k), same(l, E(c, rl(c, h), k)))

def mok(+c: Cx, t: Tree<Entry>) -> Bool:
  match t:
    case TLeaf{e}:
      ent.ok(c, e)
    case TNode{l, r}:
      Bool.and(mok(c, l), mok(c, r))

law get.go.ent:
  for +c: Cx
  for t: Tree<Entry>
  for +n: U32
  for +i: U32
  for z: Bool
  for +hm: T(mok(c, t))
  T(ent.ok(c, snd1(Entry, Array.get.go(Entry, unshadow(Entry, t), n, i, z))))

law snd1.lo:
  for -T: Data
  for -ys: Array<T>
  for r: Array<T> & T
  {snd1(T, Array.swap.lo(T, ys, r)) == snd1(T, r) : T}

def snd1.lo(T, ys, r):
  match r:
    case (a, x):
      {==}

law snd1.hi:
  for -T: Data
  for -xs: Array<T>
  for r: Array<T> & T
  {snd1(T, Array.swap.hi(T, xs, r)) == snd1(T, r) : T}

def snd1.hi(T, xs, r):
  match r:
    case (a, x):
      {==}

def get.go.ent(c, t, n, i, z, hm):
  match t z:
    case TLeaf{+x} _:
      hm
    case TNode{+l, +r} True{}:
      %Equal.sym(Entry, snd1(Entry, Array.swap.lo(Entry, unshadow(Entry, r), Array.get.go(Entry, unshadow(Entry, l), U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))))), snd1(Entry, Array.get.go(Entry, unshadow(Entry, l), U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))), snd1.lo(Entry, unshadow(Entry, r), Array.get.go(Entry, unshadow(Entry, l), U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))))) : T(ent.ok(c, _))
      get.go.ent(c, l, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))), and.l(mok(c, l), mok(c, r), hm))
    case TNode{+l, +r} False{}:
      %Equal.sym(Entry, snd1(Entry, Array.swap.hi(Entry, unshadow(Entry, l), Array.get.go(Entry, unshadow(Entry, r), U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))), snd1(Entry, Array.get.go(Entry, unshadow(Entry, r), U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))), snd1.hi(Entry, unshadow(Entry, l), Array.get.go(Entry, unshadow(Entry, r), U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))) : T(ent.ok(c, _))
      get.go.ent(c, r, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), and.r(mok(c, l), mok(c, r), hm))

law get.ent:
  for +c: Cx
  for +t: Tree<Entry>
  for +i: U32
  for +hm: T(mok(c, t))
  T(ent.ok(c, tr.rd(Entry, t, i)))

law get.ent.k:
  for +c: Cx
  for +t: Tree<Entry>
  for +n: U32
  for +i: U32
  for +hm: T(mok(c, t))
  T(ent.ok(c, snd1(Entry, Array.get.at(Entry, i, (unshadow(Entry, t), n)))))

def get.ent.k(c, t, n, i, hm):
  get.go.ent(c, t, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)), hm)

def get.ent(c, t, i, hm):
  %size.same(Entry, t) : T(ent.ok(c, snd1(Entry, Array.get.at(Entry, i, _))))
  get.ent.k(c, t, snd.u(Entry, Array.size(Entry, unshadow(Entry, t))), i, hm)

# writing a memo cell

def SwW(+c: Cx, r: Array<Entry> & Entry) -> Type:
  &t: Tree<Entry> -> &old: Entry -> {r == (unshadow(Entry, t), old) : Array<Entry> & Entry} & T(mok(c, t))

law swap.lo.k:
  for +c: Cx
  for +r: Tree<Entry>
  for +hr: T(mok(c, r))
  for -inner: Array<Entry> & Entry
  for w: SwW(c, inner)
  SwW(c, Array.swap.lo(Entry, unshadow(Entry, r), inner))

def swap.lo.k(c, r, hr, inner, w):
  match w:
    case (+t2, +old, e, hm2):
      (TNode{t2, r}, old, Equal.cong(Array<Entry> & Entry, Array<Entry> & Entry, p => Array.swap.lo(Entry, unshadow(Entry, r), p), inner, (unshadow(Entry, t2), old), e), and.i(mok(c, t2), mok(c, r), hm2, hr))

law swap.hi.k:
  for +c: Cx
  for +l: Tree<Entry>
  for +hl: T(mok(c, l))
  for -inner: Array<Entry> & Entry
  for w: SwW(c, inner)
  SwW(c, Array.swap.hi(Entry, unshadow(Entry, l), inner))

def swap.hi.k(c, l, hl, inner, w):
  match w:
    case (+t2, +old, e, hm2):
      (TNode{l, t2}, old, Equal.cong(Array<Entry> & Entry, Array<Entry> & Entry, p => Array.swap.hi(Entry, unshadow(Entry, l), p), inner, (unshadow(Entry, t2), old), e), and.i(mok(c, l), mok(c, t2), hl, hm2))

law swap.w:
  for +c: Cx
  for t: Tree<Entry>
  for +n: U32
  for +i: U32
  for +v: Entry
  for z: Bool
  for +hm: T(mok(c, t))
  for +hv: T(ent.ok(c, v))
  SwW(c, Array.swap.go(Entry, unshadow(Entry, t), n, i, v, z))

def swap.w(c, t, n, i, v, z, hm, hv):
  match t z:
    case TLeaf{+x} _:
      (TLeaf{v}, x, {==}, hv)
    case TNode{+l, +r} True{}:
      swap.lo.k(c, r, and.r(mok(c, l), mok(c, r), hm), Array.swap.go(Entry, unshadow(Entry, l), U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), swap.w(c, l, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))), and.l(mok(c, l), mok(c, r), hm), hv))
    case TNode{+l, +r} False{}:
      swap.hi.k(c, l, and.l(mok(c, l), mok(c, r), hm), Array.swap.go(Entry, unshadow(Entry, r), U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), swap.w(c, r, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), and.r(mok(c, l), mok(c, r), hm), hv))

def SetW(+c: Cx, a: Array<Entry>) -> Type:
  &t: Tree<Entry> -> {a == unshadow(Entry, t) : Array<Entry>} & T(mok(c, t))

law set.fin.k:
  for +c: Cx
  for r: Array<Entry> & Entry
  for w: SwW(c, r)
  SetW(c, Array.set.fin(Entry, r))

def set.fin.k(c, r, w):
  match w:
    case (+t2, +old, e, hm2):
      %Equal.sym(Array<Entry> & Entry, r, (unshadow(Entry, t2), old), e) : SetW(c, Array.set.fin(Entry, _))
      (t2, {==}, hm2)

law set.w:
  for +c: Cx
  for +t: Tree<Entry>
  for +i: U32
  for +v: Entry
  for +hm: T(mok(c, t))
  for +hv: T(ent.ok(c, v))
  SetW(c, Array.set(Entry, unshadow(Entry, t), i, v))

law set.w.k:
  for +c: Cx
  for +t: Tree<Entry>
  for +n: U32
  for +i: U32
  for +v: Entry
  for +hm: T(mok(c, t))
  for +hv: T(ent.ok(c, v))
  SetW(c, Array.set.fin(Entry, Array.swap.at(Entry, i, v, (unshadow(Entry, t), n))))

def set.w.k(c, t, n, i, v, hm, hv):
  set.fin.k(c, Array.swap.go(Entry, unshadow(Entry, t), n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), swap.w(c, t, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)), hm, hv))

def set.w(c, t, i, v, hm, hv):
  %size.same(Entry, t) : SetW(c, Array.set.fin(Entry, Array.swap.at(Entry, i, v, _)))
  set.w.k(c, t, snd.u(Entry, Array.size(Entry, unshadow(Entry, t))), i, v, hm, hv)

def NewW(+c: Cx, a: Array<Entry>) -> Type:
  &t: Tree<Entry> -> {a == unshadow(Entry, t) : Array<Entry>} & T(mok(c, t))

law new.k:
  for +c: Cx
  for -x: Array<Entry>
  for -y: Array<Entry>
  for w1: NewW(c, x)
  for w2: NewW(c, y)
  NewW(c, ANode{x, y})

def new.k(c, x, y, w1, w2):
  match w1:
    case (+t1, e1, h1):
      match w2:
        case (+t2, e2, h2):
          %Equal.sym(Array<Entry>, x, unshadow(Entry, t1), e1) : NewW(c, ANode{_, y})
          %Equal.sym(Array<Entry>, y, unshadow(Entry, t2), e2) : NewW(c, ANode{unshadow(Entry, t1), _})
          (TNode{t1, t2}, {==}, and.i(mok(c, t1), mok(c, t2), h1, h2))

law new.w:
  for +c: Cx
  for +d: Nat
  NewW(c, Array.new(Entry, d, ENone{}))

def new.w(c, d):
  match d:
    case 0n:
      (TLeaf{ENone{}}, {==}, {==})
    case 1n+p:
      new.k(c, Array.new(Entry, p, ENone{}), Array.new(Entry, p, ENone{}), new.w(c, p), new.w(c, p))

# reading a memo cell

def probe.v(ent: Entry, +i: U32, +w: U32) -> V:
  match ent:
    case ENone{}:
      VNone{}
    case EOk{+k, +h, +e}:
      probe.k2(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), e)

law probe.k1.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for ent: Entry
  for +i: U32
  for +w: U32
  {probe.k1(uO(c), uA(c), (unshadow(Entry, tm), ent), i, w) == OO(c, tm, probe.v(ent, i, w)) : Out}

def probe.k1.ok(c, tm, ent, i, w):
  match ent:
    case ENone{}:
      {==}
    case EOk{+k, +h, +e}:
      {==}

law probe.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for +i: U32
  for +w: U32
  {probe(uO(c), uA(c), unshadow(Entry, tm), i, w) == OO(c, tm, probe.v(tr.rd(Entry, tm, hash(i, w)), i, w)) : Out}

def probe.ok(c, tm, i, w):
  %get.same(Entry, tm, hash(i, w)) : {probe.k1(uO(c), uA(c), _, i, w) == OO(c, tm, probe.v(tr.rd(Entry, tm, hash(i, w)), i, w)) : Out}
  probe.k1.ok(c, tm, tr.rd(Entry, tm, hash(i, w)), i, w)

def mst(+f: UL, +v: V) -> Bool:
  match v:
    case VNone{}:
      True{}
    case VStuck{}:
      True{}
    case VEnds{e}:
      same(e, f)
    case VOne{+x}:
      same(UCon{x, UNil{}}, f)
    case VNode{q, x}:
      False{}

law mst.vnorm:
  for e: UL
  for +f: UL
  for +h: T(same(e, f))
  T(mst(f, vnorm(e)))

def mst.vnorm(e, f, h):
  match e:
    case UNil{}:
      h
    case UCon{+x, +t}:
      match t:
        case UNil{}:
          h
        case UCon{+y, +r}:
          h

law probe.hit:
  for +c: Cx
  for +k: U32
  for +h: U32
  for +e: UL
  for +i: U32
  for +w: U32
  for +e1: T(U32.is_eq(k, i))
  for +e2: T(U32.is_eq(h, w))
  for +hm: T(same(e, E(c, rl(c, h), k)))
  T(same(e, E(c, rl(c, w), i)))

def probe.hit(c, k, h, e, i, w, e1, e2, hm):
  %u32.eq.t(k, i, e1) : T(same(e, E(c, rl(c, w), _)))
  %u32.eq.t(h, w, e2) : T(same(e, E(c, rl(c, _), k)))
  hm

law probe.memo:
  for +c: Cx
  for ent: Entry
  for +i: U32
  for +w: U32
  for +hm: T(ent.ok(c, ent))
  T(mst(E(c, rl(c, w), i), probe.v(ent, i, w)))

law probe.k2.t:
  for b: Bool
  for +c: Cx
  for +e: UL
  for +i: U32
  for +w: U32
  for +f: UL
  for +eb: {b == True{} : Bool}
  for +h: T(same(e, f))
  T(mst(f, probe.k2(b, e)))

def probe.k2.t(b, c, e, i, w, f, eb, h):
  match b:
    case True{}:
      mst.vnorm(e, f, h)
    case False{}:
      false.elim(T(mst(f, probe.k2(False{}, e))), eb)

law probe.k2.f:
  for b: Bool
  for +e: UL
  for +f: UL
  for +eb: {b == False{} : Bool}
  T(mst(f, probe.k2(b, e)))

def probe.k2.f(b, e, f, eb):
  match b:
    case False{}:
      {==}
    case True{}:
      absurd(T(mst(f, probe.k2(True{}, e))), true.not_false(eb))

def probe.memo(c, ent, i, w, hm):
  match ent:
    case ENone{}:
      {==}
    case EOk{+k, +h, +e}:
      bool.split(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), T(mst(E(c, rl(c, w), i), probe.k2(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), e))), +eb => probe.k2.t(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), c, e, i, w, E(c, rl(c, w), i), eb, probe.hit(c, k, h, e, i, w, and.l(U32.is_eq(k, i), U32.is_eq(h, w), eb), and.r(U32.is_eq(k, i), U32.is_eq(h, w), eb), and.r(cell(c, k), same(e, E(c, rl(c, h), k)), hm))), +eb => probe.k2.f(Bool.and(U32.is_eq(k, i), U32.is_eq(h, w)), e, E(c, rl(c, w), i), eb))
# ---- guards are sound ----

law not.of.f:
  for b: Bool
  for +e: {b == False{} : Bool}
  T(Bool.not(b))

def not.of.f(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      absurd(T(Bool.not(True{})), true.not_false(e))

law ckf.lit:
  for +c: Cx
  for +kd: Kd
  for +id: U32
  for +cx: U32
  for +k: U32
  for +hv: T(imp.b(Bool.not(U32.is_ge(cx, 128)), allow(c, kd, id, cx)))
  for +hf: T(U32.is_eq(cx, k))
  for +hk: {U32.is_ge(k, 128) == False{} : Bool}
  T(allow(c, kd, id, k))

law ge.tr:
  for +cx: U32
  for +k: U32
  for +e: T(U32.is_eq(cx, k))
  for +hk: {U32.is_ge(k, 128) == False{} : Bool}
  {U32.is_ge(cx, 128) == False{} : Bool}

def ge.tr(cx, k, e, hk):
  %u32.eq.t(k, cx, u32.eq.sym(cx, k, e)) : {U32.is_ge(_, 128) == False{} : Bool}
  hk

def ckf.lit(c, kd, id, cx, k, hv, hf, hk):
  %u32.eq.t(cx, k, hf) : T(allow(c, kd, id, _))
  imp.e(Bool.not(U32.is_ge(cx, 128)), allow(c, kd, id, cx), hv, not.of.f(U32.is_ge(cx, 128), ge.tr(cx, k, hf, hk)))

law ckf.sound:
  for +fl: Nat
  for +r: R
  for +c: Cx
  for +kd: Kd
  for +id: U32
  for +k: U32
  for +hv: T(ckf(c, kd, fl, r, id))
  for +hf: T(fst(fl, cg2(c), r, k))
  for +hk: {U32.is_ge(k, 128) == False{} : Bool}
  T(allow(c, kd, id, k))

def ckf.sound(fl, r, c, kd, id, k, hv, hf, hk):
  match fl:
    case 0n:
      all.at(c, PAll{kd, id}, k, hv, hk)
    case 1n+p:
      match r:
        case Emp{}:
          false.elim(T(allow(c, kd, id, k)), hf)
        case Bad{}:
          false.elim(T(allow(c, kd, id, k)), hf)
        case Lit{+x}:
          ckf.lit(c, kd, id, Char.to_u32(x), k, hv, hf, hk)
        case Rng{+x, +y}:
          imp.e(isle(x, k, y), allow(c, kd, id, k), all.at(c, PRg{kd, id, x, y}, k, hv, hk), hf)
        case Cat{+a1, +b1}:
          or.c(fst(fl, cg2(c), a1, k), Bool.and(nul(fl, cg2(c), a1), fst(fl, cg2(c), b1, k)), T(allow(c, kd, id, k)), hf, +h1 => ckf.sound(fl, a1, c, kd, id, k, and.l(ckf(c, kd, fl, a1, id), imp.b(nul(fl, cg2(c), a1), ckf(c, kd, fl, b1, id)), hv), h1, hk), +h2 => ckf.sound(fl, b1, c, kd, id, k, imp.e(nul(fl, cg2(c), a1), ckf(c, kd, fl, b1, id), and.r(ckf(c, kd, fl, a1, id), imp.b(nul(fl, cg2(c), a1), ckf(c, kd, fl, b1, id)), hv), and.l(nul(fl, cg2(c), a1), fst(fl, cg2(c), b1, k), h2)), and.r(nul(fl, cg2(c), a1), fst(fl, cg2(c), b1, k), h2), hk))
        case Alt{+a1, +b1}:
          or.c(fst(fl, cg2(c), a1, k), fst(fl, cg2(c), b1, k), T(allow(c, kd, id, k)), hf, +h1 => ckf.sound(fl, a1, c, kd, id, k, and.l(ckf(c, kd, fl, a1, id), ckf(c, kd, fl, b1, id), hv), h1, hk), +h2 => ckf.sound(fl, b1, c, kd, id, k, and.r(ckf(c, kd, fl, a1, id), ckf(c, kd, fl, b1, id), hv), h2, hk))
        case Star{+x}:
          ckf.sound(fl, x, c, kd, id, k, hv, hf, hk)
        case Ref{+n}:
          ckf.sound(p, lk(cg2(c), n), c, kd, id, k, hv, hf, hk)

law ckm.sound:
  for +c: Cx
  for +kd: Kd
  for +y: R
  for +id: U32
  for +k: U32
  for +hv: T(ckm(c, kd, y, id))
  for +hm: T(may(3n, cg2(c), y, k))
  for +hk: {U32.is_ge(k, 128) == False{} : Bool}
  T(allow(c, kd, id, k))

def ckm.sound(c, kd, y, id, k, hv, hm, hk):
  or.c(nul(3n, cg2(c), y), fst(3n, cg2(c), y, k), T(allow(c, kd, id, k)), hm, +hn => all.at(c, PAll{kd, id}, k, imp.e(nul(3n, cg2(c), y), all128(c, PAll{kd, id}, 128n, 0), and.l(imp.b(nul(3n, cg2(c), y), all128(c, PAll{kd, id}, 128n, 0)), ckf(c, kd, 3n, y, id), hv), hn), hk), +hf => ckf.sound(3n, y, c, kd, id, k, and.r(imp.b(nul(3n, cg2(c), y), all128(c, PAll{kd, id}, 128n, 0)), ckf(c, kd, 3n, y, id), hv), hf, hk))

law may.fi:
  for q: String
  for +c: Cx
  for +y2: String
  for +y: R
  for +z: U32
  for +hx: T(at(c, q ++ y2, z))
  for +hfi: T(fi(3n, cg2(c), y, q))
  T(may(3n, cg2(c), y, rdA(c, z)))

def may.fi(q, c, y2, y, z, hx, hfi):
  match q:
    case SNil{}:
      may.nil(c, y, rdA(c, z), hfi)
    case SCon{+x, +t}:
      may.con(c, y, x, t, rdA(c, z), at.head(c, x, t ++ y2, z, hx), hfi)

law tr.at:
  for +c: Cx
  for -x: String
  for -y: String
  for +z: U32
  for +e: {x == y : String}
  for +h: T(at(c, x, z))
  T(at(c, y, z))

def tr.at(c, x, y, z, e, h):
  %e : T(at(c, _, z))
  h

law may.of.k2:
  for +c: Cx
  for +y: R
  for +z: U32
  for +q: String
  for +y2: String
  for +hx: T(at(c, suf(c, z), z))
  for +e1: {q ++ y2 == suf(c, z) : String}
  for +ht: T(TR(c, y, q))
  for wit: CellW(c, z)
  T(may(3n, cg2(c), y, rdA(c, z)))

def may.of.k2(c, y, z, q, y2, hx, e1, ht, wit):
  match wit:
    case (+u, +eu, ep):
      may.fi(q, c, y2, y, z, tr.at(c, suf(c, z), q ++ y2, z, Equal.sym(String, q ++ y2, suf(c, z), e1), hx), fi.ok(c, 3n, y, 1n, 0n, q, u, y2, sub.of.cell(c, u, q, y2, z, eu, e1), ht))

law may.of.k1:
  for +c: Cx
  for +y: R
  for +z: U32
  for +w: U32
  for +hx: T(at(c, suf(c, z), z))
  for +hc: T(cell(c, z))
  for h: EW(c, y, "", suf(c, z), z, w)
  T(may(3n, cg2(c), y, rdA(c, z)))

def may.of.k1(c, y, z, w, hx, hc, h):
  match h:
    case (+q, +y2, +e1, e2, ht):
      may.of.k2(c, y, z, q, y2, hx, e1, ht, cell.elim(c, z, hc))

law may.of.E:
  for +c: Cx
  for +y: R
  for +z: U32
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hw: T(has(w, E(c, y, z)))
  T(may(3n, cg2(c), y, rdA(c, z)))

def may.of.E(c, y, z, w, ga, hc, hw):
  may.of.k1(c, y, z, w, at.suf(c, z, ga, hc), hc, E.elim(c, y, suf(c, z), "", z, w, hw))

law true.false.e:
  for -b: Bool
  for +h1: {b == True{} : Bool}
  for +h2: {b == False{} : Bool}
  Empty

def true.false.e(b, h1, h2):
  true.not_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, h1), h2))

law kept.contra:
  for big: Bool
  for +c: Cx
  for +id: U32
  for +ch: U32
  for +y: R
  for +hb: {big == U32.is_ge(ch, 128) : Bool}
  for +hkf: {kept.go(big, c, id, ch) == False{} : Bool}
  for +hv: T(ckm(c, KBit{}, y, id))
  for +hm: T(may(3n, cg2(c), y, ch))
  Empty

def kept.contra(big, c, id, ch, y, hb, hkf, hv, hm):
  match big:
    case True{}:
      true.not_false(hkf)
    case False{}:
      true.false.e(U32.is_eq(rdA(c, ((id + 1 : U32) + ch : U32)), 1), ckm.sound(c, KBit{}, y, id, ch, hv, hm, Equal.sym(Bool, False{}, U32.is_ge(ch, 128), hb)), hkf)

law kept.no:
  for +c: Cx
  for +id: U32
  for +z: U32
  for +y: R
  for +w: U32
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hkf: {kept(c, id, z) == False{} : Bool}
  for +hv: T(ckm(c, KBit{}, y, id))
  for +hw: T(has(w, E(c, y, z)))
  Empty

def kept.no(c, id, z, y, w, ga, hc, hkf, hv, hw):
  kept.contra(U32.is_ge(rdA(c, z), 128), c, id, rdA(c, z), y, {==}, hkf, hv, may.of.E(c, y, z, w, ga, hc, hw))

# ---- what filtering changes ----

law U.fil.k:
  for +c: Cx
  for +y: R
  for +id: U32
  for +F: UL
  for +w: U32
  for +ga: T(Glob(c))
  for +hF: T(cells(c, F))
  for +hv: T(ckm(c, KBit{}, y, id))
  for u: UW(c, y, F, w)
  T(has(w, U(c, y, fil(c, id, F))))

def U.fil.k(c, y, id, F, w, ga, hF, hv, u):
  match u:
    case (+z, +hz, +hw):
      bool.split(kept(c, id, z), T(has(w, U(c, y, fil(c, id, F)))), +hk => U.in(c, y, fil(c, id, F), z, w, hw, fil.in(F, c, id, z, hk, hz)), +hkf => absurd(T(has(w, U(c, y, fil(c, id, F)))), kept.no(c, id, z, y, w, ga, cells.has(c, F, z, hF, hz), hkf, hv, hw)))

law U.fil:
  for l: UL
  for +c: Cx
  for +y: R
  for +id: U32
  for +F: UL
  for +ga: T(Glob(c))
  for +hF: T(cells(c, F))
  for +hv: T(ckm(c, KBit{}, y, id))
  for +hl: T(sub(l, U(c, y, F)))
  T(sub(l, U(c, y, fil(c, id, F))))

def U.fil(l, c, y, id, F, ga, hF, hv, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, U(c, y, fil(c, id, F)), U.fil.k(c, y, id, F, w, ga, hF, hv, U.elim(c, y, F, w, sub.head(w, t, U(c, y, F), hl))), U.fil(t, c, y, id, F, ga, hF, hv, sub.tail(w, t, U(c, y, F), hl)))

law U.mono.k:
  for +c: Cx
  for +y: R
  for +a: UL
  for +b: UL
  for +w: U32
  for +hs: T(sub(a, b))
  for u: UW(c, y, a, w)
  T(has(w, U(c, y, b)))

def U.mono.k(c, y, a, b, w, hs, u):
  match u:
    case (+z, +hz, +hw):
      U.in(c, y, b, z, w, hw, sub.has(z, a, b, hs, hz))

law U.mono:
  for l: UL
  for +c: Cx
  for +y: R
  for +a: UL
  for +b: UL
  for +hs: T(sub(a, b))
  for +hl: T(sub(l, U(c, y, a)))
  T(sub(l, U(c, y, b)))

def U.mono(l, c, y, a, b, hs, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, U(c, y, b), U.mono.k(c, y, a, b, w, hs, U.elim(c, y, a, w, sub.head(w, t, U(c, y, a), hl))), U.mono(t, c, y, a, b, hs, sub.tail(w, t, U(c, y, a), hl)))

law U.same:
  for +c: Cx
  for +y: R
  for +a: UL
  for +b: UL
  for +h: T(same(a, b))
  T(same(U(c, y, a), U(c, y, b)))

def U.same(c, y, a, b, h):
  same.i(U(c, y, a), U(c, y, b), U.mono(U(c, y, a), c, y, a, b, same.l(a, b, h), sub.refl(U(c, y, a))), U.mono(U(c, y, b), c, y, b, a, same.r(a, b, h), sub.refl(U(c, y, b))))

law fil.self:
  for l: UL
  for +c: Cx
  for +kt: U32
  for +F: UL
  for +hl: T(sub(l, fil(c, kt, F)))
  T(sub(l, F))

def fil.self(l, c, kt, F, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, F, fil.has(F, c, kt, w, sub.head(w, t, fil(c, kt, F), hl)), fil.self(t, c, kt, F, sub.tail(w, t, fil(c, kt, F), hl)))

law U.fil.same:
  for +c: Cx
  for +y: R
  for +id: U32
  for +F: UL
  for +ga: T(Glob(c))
  for +hF: T(cells(c, F))
  for +hv: T(ckm(c, KBit{}, y, id))
  T(same(U(c, y, fil(c, id, F)), U(c, y, F)))

def U.fil.same(c, y, id, F, ga, hF, hv):
  same.i(U(c, y, fil(c, id, F)), U(c, y, F), U.mono(U(c, y, fil(c, id, F)), c, y, fil(c, id, F), F, fil.self(fil(c, id, F), c, id, F, sub.refl(fil(c, id, F))), sub.refl(U(c, y, fil(c, id, F)))), U.fil(U(c, y, F), c, y, id, F, ga, hF, hv, sub.refl(U(c, y, F))))

law kept.one.go:
  for big: Bool
  for +c: Cx
  for +id: U32
  for +ch: U32
  for +hb: {big == U32.is_ge(ch, 128) : Bool}
  for +h: T(all128(c, POne{id}, 128n, 0))
  T(kept.go(big, c, id, ch))

def kept.one.go(big, c, id, ch, hb, h):
  match big:
    case True{}:
      {==}
    case False{}:
      all.at(c, POne{id}, ch, h, Equal.sym(Bool, False{}, U32.is_ge(ch, 128), hb))

law fil.one:
  for l: UL
  for +c: Cx
  for +id: U32
  for +F: UL
  for +ho: T(all128(c, POne{id}, 128n, 0))
  for +hl: T(sub(l, F))
  T(sub(l, fil(c, id, F)))

def fil.one(l, c, id, F, ho, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      sub.cons(w, t, fil(c, id, F), fil.in(F, c, id, w, kept.one.go(U32.is_ge(rdA(c, w), 128), c, id, rdA(c, w), {==}, ho), sub.head(w, t, F, hl)), fil.one(t, c, id, F, ho, sub.tail(w, t, F, hl)))

law fil.one.same:
  for +c: Cx
  for +id: U32
  for +F: UL
  for +ho: T(all128(c, POne{id}, 128n, 0))
  T(same(fil(c, id, F), F))

def fil.one.same(c, id, F, ho):
  same.i(fil(c, id, F), F, fil.self(fil(c, id, F), c, id, F, sub.refl(fil(c, id, F))), fil.one(F, c, id, F, ho, sub.refl(F)))

# ---- selection between alternatives ----

def selq(q: Op, ma: Bool, mb: Bool) -> Bool:
  match q:
    case ASelL{}:
      Bool.not(mb)
    case ASelR{}:
      Bool.not(ma)
    case ASelN{}:
      Bool.and(Bool.not(ma), Bool.not(mb))
    case _:
      True{}

# ---- alternation at a cell ----

law sel.of.al:
  for q: Op
  for ma: Bool
  for mb: Bool
  for +hl: T(imp.b(ma, al.l(q)))
  for +hr: T(imp.b(mb, al.r(q)))
  T(selq(q, ma, mb))

def sel.of.al(q, ma, mb, hl, hr):
  match q:
    case OLit{}:
      {==}
    case OCls{}:
      {==}
    case OAlt{}:
      {==}
    case OCat{}:
      {==}
    case OCatS{}:
      {==}
    case OCatSC{}:
      {==}
    case OStar{}:
      {==}
    case OStarC{}:
      {==}
    case ORefM{}:
      {==}
    case ORef{}:
      {==}
    case OEmp{}:
      {==}
    case OBad{}:
      {==}
    case ASelB{}:
      {==}
    case ASelL{}:
      match mb:
        case True{}:
          false.elim(T(Bool.not(True{})), hr)
        case False{}:
          {==}
    case ASelR{}:
      match ma:
        case True{}:
          false.elim(T(Bool.not(True{})), hl)
        case False{}:
          {==}
    case ASelN{}:
      match ma mb:
        case True{} True{}:
          false.elim(T(False{}), hl)
        case True{} False{}:
          false.elim(T(False{}), hl)
        case False{} True{}:
          false.elim(T(False{}), hr)
        case False{} False{}:
          {==}

def altpre(+c: Cx, +a: R, +b: R, +ch: U32, v: V) -> Bool:
  match v:
    case VNode{q, x}:
      selq(q, may(3n, cg2(c), a, ch), may(3n, cg2(c), b, ch))
    case _:
      False{}

law altpre.ok:
  for big: Bool
  for +c: Cx
  for +a: R
  for +b: R
  for +id: U32
  for +ch: U32
  for +hb: {big == U32.is_ge(ch, 128) : Bool}
  for +hL: T(ckm(c, KL{}, a, id))
  for +hR: T(ckm(c, KR{}, b, id))
  T(altpre(c, a, b, ch, altv(c, big, id, ch)))

def altpre.ok(big, c, a, b, id, ch, hb, hL, hR):
  match big:
    case True{}:
      {==}
    case False{}:
      sel.of.al(rdO(c, ((id + 1 : U32) + ch : U32)), may(3n, cg2(c), a, ch), may(3n, cg2(c), b, ch), imp.i(may(3n, cg2(c), a, ch), al.l(rdO(c, ((id + 1 : U32) + ch : U32))), +hm => ckm.sound(c, KL{}, a, id, ch, hL, hm, Equal.sym(Bool, False{}, U32.is_ge(ch, 128), hb))), imp.i(may(3n, cg2(c), b, ch), al.r(rdO(c, ((id + 1 : U32) + ch : U32))), +hm => ckm.sound(c, KR{}, b, id, ch, hR, hm, Equal.sym(Bool, False{}, U32.is_ge(ch, 128), hb))))

law none.sub:
  for l: UL
  for +c: Cx
  for +y: R
  for +z: U32
  for +hnm: {may(3n, cg2(c), y, rdA(c, z)) == False{} : Bool}
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  for +hl: T(sub(l, E(c, y, z)))
  T(sub(l, UNil{}))

def none.sub(l, c, y, z, hnm, ga, hc, hl):
  match l:
    case UNil{}:
      {==}
    case UCon{+w, +t}:
      absurd(T(sub(UCon{w, t}, UNil{})), true.false.e(may(3n, cg2(c), y, rdA(c, z)), may.of.E(c, y, z, w, ga, hc, sub.head(w, t, E(c, y, z), hl)), hnm))

law none.E:
  for +c: Cx
  for +y: R
  for +z: U32
  for +hnm: T(Bool.not(may(3n, cg2(c), y, rdA(c, z))))
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(sub(E(c, y, z), UNil{}))

def none.E(c, y, z, hnm, ga, hc):
  none.sub(E(c, y, z), c, y, z, not.f(may(3n, cg2(c), y, rdA(c, z)), hnm), ga, hc, sub.refl(E(c, y, z)))

law alt.l.same:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +h: T(sub(E(c, b, z), UNil{}))
  T(same(E(c, a, z), E(c, Alt{a, b}, z)))

def alt.l.same(c, a, b, z, h):
  same.trans(E(c, a, z), uapp(E(c, a, z), E(c, b, z)), E(c, Alt{a, b}, z), same.i(E(c, a, z), uapp(E(c, a, z), E(c, b, z)), sub.uapp.l(E(c, a, z), E(c, a, z), E(c, b, z), sub.refl(E(c, a, z))), uapp.sub(E(c, a, z), E(c, b, z), E(c, a, z), sub.refl(E(c, a, z)), sub.trans(E(c, b, z), UNil{}, E(c, a, z), h, {==}))), alt.same(c, a, b, z))

law alt.r.same:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +h: T(sub(E(c, a, z), UNil{}))
  T(same(E(c, b, z), E(c, Alt{a, b}, z)))

def alt.r.same(c, a, b, z, h):
  same.trans(E(c, b, z), uapp(E(c, a, z), E(c, b, z)), E(c, Alt{a, b}, z), same.i(E(c, b, z), uapp(E(c, a, z), E(c, b, z)), sub.uapp.r(E(c, b, z), E(c, a, z), E(c, b, z), sub.refl(E(c, b, z))), uapp.sub(E(c, a, z), E(c, b, z), E(c, b, z), sub.trans(E(c, a, z), UNil{}, E(c, b, z), h, {==}), sub.refl(E(c, b, z)))), alt.same(c, a, b, z))

law alt.n.same:
  for +c: Cx
  for +a: R
  for +b: R
  for +z: U32
  for +h1: T(sub(E(c, a, z), UNil{}))
  for +h2: T(sub(E(c, b, z), UNil{}))
  T(same(UNil{}, E(c, Alt{a, b}, z)))

def alt.n.same(c, a, b, z, h1, h2):
  same.trans(UNil{}, uapp(E(c, a, z), E(c, b, z)), E(c, Alt{a, b}, z), same.i(UNil{}, uapp(E(c, a, z), E(c, b, z)), {==}, uapp.sub(E(c, a, z), E(c, b, z), UNil{}, h1, h2)), alt.same(c, a, b, z))

# ---- results ----

def Pst(+c: Cx, +F: UL, o: Out) -> Type:
  &tm: Tree<Entry> -> &v: V -> {o == OO(c, tm, v) : Out} & T(mok(c, tm)) & T(ex(F, v))

law pst.bind:
  for +c: Cx
  for +F1: UL
  for +F2: UL
  for -G: Out -> Out
  for -o: Out
  for h: Pst(c, F1, o)
  for k: @tm: Tree<Entry> -> @v: V -> T(mok(c, tm)) -> T(ex(F1, v)) -> Pst(c, F2, G(OO(c, tm, v)))
  Pst(c, F2, G(o))

def pst.bind(c, F1, F2, G, o, h, k):
  match h:
    case (+tm, +v, e, hm, hv):
      %Equal.sym(Out, o, OO(c, tm, v), e) : Pst(c, F2, G(_))
      k(tm, v, hm, hv)

law pst.conv:
  for +c: Cx
  for +F: UL
  for +G: UL
  for -o: Out
  for +hs: T(same(F, G))
  for h: Pst(c, F, o)
  Pst(c, G, o)

def pst.conv(c, F, G, o, hs, h):
  match h:
    case (+tm, +v, e, hm, hv):
      (tm, v, e, hm, ex.same(F, G, v, hs, hv))

law store.k:
  for +c: Cx
  for +tm: Tree<Entry>
  for +i: U32
  for +w: U32
  for +e: UL
  for v0: V
  for +F: UL
  for +hv: T(ex(F, v0))
  for w0: SetW(c, Array.set(Entry, unshadow(Entry, tm), hash(i, w), EOk{i, w, e}))
  Pst(c, F, O{uO(c), uA(c), Array.set(Entry, unshadow(Entry, tm), hash(i, w), EOk{i, w, e}), v0})

def store.k(c, tm, i, w, e, v0, F, hv, w0):
  match w0:
    case (+t2, e2, hm2):
      (t2, v0, Equal.cong(Array<Entry>, Out, m => O{uO(c), uA(c), m, v0}, Array.set(Entry, unshadow(Entry, tm), hash(i, w), EOk{i, w, e}), unshadow(Entry, t2), e2), hm2, hv)

law store.ok:
  for +c: Cx
  for +tm: Tree<Entry>
  for v: V
  for +i: U32
  for +w: U32
  for +hm: T(mok(c, tm))
  for +hc: T(cell(c, i))
  for +hv: T(ex(E(c, rl(c, w), i), v))
  Pst(c, E(c, rl(c, w), i), store(OO(c, tm, v), i, w))

def store.ok(c, tm, v, i, w, hm, hc, hv):
  match v:
    case VNone{}:
      false.elim(Pst(c, E(c, rl(c, w), i), store(OO(c, tm, VNone{}), i, w)), hv)
    case VStuck{}:
      (tm, VStuck{}, {==}, hm, {==})
    case VEnds{+e}:
      store.k(c, tm, i, w, e, VEnds{e}, E(c, rl(c, w), i), hv, set.w(c, tm, hash(i, w), EOk{i, w, e}, hm, and.i(cell(c, i), same(e, E(c, rl(c, w), i)), hc, hv)))
    case VOne{+x}:
      store.k(c, tm, i, w, UCon{x, UNil{}}, VOne{x}, E(c, rl(c, w), i), hv, set.w(c, tm, hash(i, w), EOk{i, w, UCon{x, UNil{}}}, hm, and.i(cell(c, i), same(UCon{x, UNil{}}, E(c, rl(c, w), i)), hc, hv)))
    case VNode{q, x}:
      false.elim(Pst(c, E(c, rl(c, w), i), store(OO(c, tm, VNode{q, x}), i, w)), hv)

# ---- the class scanner ----

law leaf.same.k:
  for b: Bool
  for +c: Cx
  for +r: R
  for +z: U32
  for +hx: T(ex(E(c, r, z), single(b, z)))
  T(same(pickc(b, (z + 1 : U32), UNil{}), E(c, r, z)))

def leaf.same.k(b, c, r, z, hx):
  match b:
    case True{}:
      hx
    case False{}:
      hx

law leaf.same:
  for +c: Cx
  for +r: R
  for +z: U32
  for +b: Bool
  for +hb: {b == cmatch(r, rdA(c, z)) : Bool}
  for +hl: T(leafy(r))
  for +hne: T(Bool.not(cmatch(r, END)))
  for +ga: T(Glob(c))
  for +hc: T(cell(c, z))
  T(same(pickc(b, (z + 1 : U32), UNil{}), E(c, r, z)))

def leaf.same(c, r, z, b, hb, hl, hne, ga, hc):
  leaf.same.k(b, c, r, z, leaf.ex(c, r, z, b, hb, hl, hne, ga, hc))

law step.inv:
  for +c: Cx
  for +z: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +i: U32
  for +acc: UL
  for +ga: T(Glob(c))
  for +b: Bool
  for +hb: {b == cmatch(z, rdA(c, i)) : Bool}
  for +hl: T(leafy(z))
  for +hne: T(Bool.not(cmatch(z, END)))
  for +h: T(Inv(c, z, i0, kt, V, UCon{i, UNil{}}, acc))
  T(Inv(c, z, i0, kt, UCon{i, V}, pickc(b, (i + 1 : U32), UNil{}), pickc(kept(c, kt, i), i, acc)))

def step.inv(c, z, i0, kt, V, i, acc, ga, b, hb, hl, hne, h):
  +hcl = cells.has(c, uapp(V, UCon{i, UNil{}}), i, inv.p4(c, z, i0, kt, V, UCon{i, UNil{}}, acc, h), uapp.in.r(i, V, UCon{i, UNil{}}, has.self(i, UNil{})))
  +hs = leaf.same(c, z, i, b, hb, hl, hne, ga, hcl)
  inv.step(c, z, i0, kt, V, i, UNil{}, pickc(b, (i + 1 : U32), UNil{}), acc, ga, h, sub.weak(E(c, z, i), i, uapp(V, pickc(b, (i + 1 : U32), UNil{})), sub.uapp.r(E(c, z, i), V, pickc(b, (i + 1 : U32), UNil{}), same.r(pickc(b, (i + 1 : U32), UNil{}), E(c, z, i), hs))), same.l(pickc(b, (i + 1 : U32), UNil{}), E(c, z, i), hs), {==})

def ScW(+c: Cx, +F: UL, p: Array<U32> & V) -> Type:
  &v: V -> {p == (uA(c), v) : Array<U32> & V} & T(ex(F, v))

law tr.pk:
  for +c: Cx
  for +z: R
  for +i0: U32
  for +kt: U32
  for +V: UL
  for +L: UL
  for -k1: Bool
  for -k2: Bool
  for +i: U32
  for +acc: UL
  for +e: {k1 == k2 : Bool}
  for +h: T(Inv(c, z, i0, kt, V, L, pickc(k1, i, acc)))
  T(Inv(c, z, i0, kt, V, L, pickc(k2, i, acc)))

def tr.pk(c, z, i0, kt, V, L, k1, k2, i, acc, e, h):
  %e : T(Inv(c, z, i0, kt, V, L, pickc(_, i, acc)))
  h

law scan.fin:
  for +c: Cx
  for +z: R
  for +i0: U32
  for +gid: U32
  for +V: UL
  for +acc: UL
  for +ga: T(Glob(c))
  for +h: T(Inv(c, z, i0, gid, V, UNil{}, acc))
  T(ex(fil(c, gid, E(c, Star{z}, i0)), vnorm(rev(acc))))

def scan.fin(c, z, i0, gid, V, acc, ga, h):
  ex.vnorm(rev(acc), fil(c, gid, E(c, Star{z}, i0)), same.trans(rev(acc), acc, fil(c, gid, E(c, Star{z}, i0)), rev.same(acc), inv.fin(c, z, i0, gid, V, acc, ga, h)))

law scanf.ok:
  for +n: Nat
  for +c: Cx
  for +z: R
  for +i0: U32
  for +tb: U32
  for +gid: U32
  for +V: UL
  for +i: U32
  for +acc: UL
  for k: Bool
  for cn: Bool
  for +ga: T(Glob(c))
  for +hv: T(clso(c, z, tb))
  for +hinv: T(Inv(c, z, i0, gid, V, UCon{i, UNil{}}, acc))
  for +hk: {k == kept(c, gid, i) : Bool}
  for +hc: {cn == cmatch(z, rdA(c, i)) : Bool}
  ScW(c, fil(c, gid, E(c, Star{z}, i0)), scanf(n, tb, gid, i, acc, (uA(c), F{k, cn})))

def scanf.ok(n, c, z, i0, tb, gid, V, i, acc, k, cn, ga, hv, hinv, hk, hc):
  match n:
    case 0n:
      (VStuck{}, {==}, {==})
    case 1n+m:
      match k cn:
        case True{} True{}:
          %Equal.sym(Array<U32> & F, step(uA(c), tb, gid, (i + 1 : U32)), (uA(c), F{kept(c, gid, (i + 1 : U32)), cmatch(z, rdA(c, (i + 1 : U32)))}), step.ok(c, z, tb, gid, (i + 1 : U32), hv)) : ScW(c, fil(c, gid, E(c, Star{z}, i0)), scanf(m, tb, gid, (i + 1 : U32), UCon{i, acc}, _))
          scanf.ok(m, c, z, i0, tb, gid, UCon{i, V}, (i + 1 : U32), UCon{i, acc}, kept(c, gid, (i + 1 : U32)), cmatch(z, rdA(c, (i + 1 : U32))), ga, hv, tr.pk(c, z, i0, gid, UCon{i, V}, pickc(True{}, (i + 1 : U32), UNil{}), kept(c, gid, i), True{}, i, acc, Equal.sym(Bool, True{}, kept(c, gid, i), hk), step.inv(c, z, i0, gid, V, i, acc, ga, True{}, hc, clso.leafy(c, z, tb, hv), clso.nend(c, z, tb, hv), hinv)), {==}, {==})
        case False{} True{}:
          %Equal.sym(Array<U32> & F, step(uA(c), tb, gid, (i + 1 : U32)), (uA(c), F{kept(c, gid, (i + 1 : U32)), cmatch(z, rdA(c, (i + 1 : U32)))}), step.ok(c, z, tb, gid, (i + 1 : U32), hv)) : ScW(c, fil(c, gid, E(c, Star{z}, i0)), scanf(m, tb, gid, (i + 1 : U32), acc, _))
          scanf.ok(m, c, z, i0, tb, gid, UCon{i, V}, (i + 1 : U32), acc, kept(c, gid, (i + 1 : U32)), cmatch(z, rdA(c, (i + 1 : U32))), ga, hv, tr.pk(c, z, i0, gid, UCon{i, V}, pickc(True{}, (i + 1 : U32), UNil{}), kept(c, gid, i), False{}, i, acc, Equal.sym(Bool, False{}, kept(c, gid, i), hk), step.inv(c, z, i0, gid, V, i, acc, ga, True{}, hc, clso.leafy(c, z, tb, hv), clso.nend(c, z, tb, hv), hinv)), {==}, {==})
        case True{} False{}:
          (vnorm(rev(UCon{i, acc})), {==}, scan.fin(c, z, i0, gid, UCon{i, V}, UCon{i, acc}, ga, tr.pk(c, z, i0, gid, UCon{i, V}, pickc(False{}, (i + 1 : U32), UNil{}), kept(c, gid, i), True{}, i, acc, Equal.sym(Bool, True{}, kept(c, gid, i), hk), step.inv(c, z, i0, gid, V, i, acc, ga, False{}, hc, clso.leafy(c, z, tb, hv), clso.nend(c, z, tb, hv), hinv))))
        case False{} False{}:
          (vnorm(rev(acc)), {==}, scan.fin(c, z, i0, gid, UCon{i, V}, acc, ga, tr.pk(c, z, i0, gid, UCon{i, V}, pickc(False{}, (i + 1 : U32), UNil{}), kept(c, gid, i), False{}, i, acc, Equal.sym(Bool, False{}, kept(c, gid, i), hk), step.inv(c, z, i0, gid, V, i, acc, ga, False{}, hc, clso.leafy(c, z, tb, hv), clso.nend(c, z, tb, hv), hinv))))

law scan.pst:
  for +c: Cx
  for +tm: Tree<Entry>
  for +F: UL
  for -p: Array<U32> & V
  for +hm: T(mok(c, tm))
  for w: ScW(c, F, p)
  Pst(c, F, scan.o(uO(c), unshadow(Entry, tm), p))

def scan.pst(c, tm, F, p, hm, w):
  match w:
    case (+v, e, hv):
      %Equal.sym(Array<U32> & V, p, (uA(c), v), e) : Pst(c, F, scan.o(uO(c), unshadow(Entry, tm), _))
      (tm, v, {==}, hm, hv)
# ---- the interpreter ----

type K is Data:
  KNode{r: R}
  KCat{b: R, Fl: UL}
  KCatL{b: R}
  KCatA{b: R, y: U32}
  KAlt{a: R, b: R}
  KAltR{b: R, Fl: UL}
  KAltM{F1: UL, F2: UL}
  KStarH{a: R, Vs: UL, i0: U32}
  KStarA{a: R, Vs: UL, i0: U32}
  KStarK{a: R, Vs: UL, i0: U32}
  KRefM{}
  KStore{}

def st.of(k: K) -> St:
  match k:
    case KNode{r}:
      SNode{}
    case KCat{b, Fl}:
      SCat{}
    case KCatL{b}:
      SCatL{}
    case KCatA{b, y}:
      SCatA{}
    case KAlt{a, b}:
      SAlt{}
    case KAltR{b, Fl}:
      SAltR{}
    case KAltM{F1, F2}:
      SAltM{}
    case KStarH{a, Vs, i0}:
      SStarH{}
    case KStarA{a, Vs, i0}:
      SStarA{}
    case KStarK{a, Vs, i0}:
      SStarK{}
    case KRefM{}:
      SRefM{}
    case KStore{}:
      SStore{}

def tgt(+c: Cx, k: K, +id: U32, +i: U32, +w: U32, +L: UL, +acc: UL) -> UL:
  match k:
    case KNode{+r}:
      E(c, r, i)
    case KCat{+b, +Fl}:
      U(c, b, Fl)
    case KCatL{+b}:
      uapp(acc, U(c, b, L))
    case KCatA{+b, +y}:
      uapp(acc, uapp(E(c, b, y), U(c, b, L)))
    case KAlt{+a, +b}:
      E(c, Alt{a, b}, i)
    case KAltR{+b, +Fl}:
      uapp(Fl, E(c, b, i))
    case KAltM{+F1, +F2}:
      uapp(F1, F2)
    case KStarH{+a, +Vs, +i0}:
      fil(c, id, E(c, Star{a}, i0))
    case KStarA{+a, +Vs, +i0}:
      fil(c, id, E(c, Star{a}, i0))
    case KStarK{+a, +Vs, +i0}:
      fil(c, id, E(c, Star{a}, i0))
    case KRefM{}:
      E(c, rl(c, w), i)
    case KStore{}:
      E(c, rl(c, w), i)

def pre(+c: Cx, k: K, +id: U32, +i: U32, +w: U32, +L: UL, +acc: UL, +v: V) -> Bool:
  match k:
    case KNode{+r}:
      match v:
        case VNode{+q, +x}:
          Bool.and(nok.at(c, r, q, x, id), cell(c, i))
        case _:
          False{}
    case KCat{+b, +Fl}:
      Bool.and(ex(Fl, v), Bool.and(nok(c, b, high(w)), cells(c, Fl)))
    case KCatL{+b}:
      Bool.and(cells(c, L), nok(c, b, high(w)))
    case KCatA{+b, +y}:
      Bool.and(ex(E(c, b, y), v), Bool.and(cells(c, L), nok(c, b, high(w))))
    case KAlt{+a, +b}:
      Bool.and(altpre(c, a, b, rdA(c, i), v), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))))
    case KAltR{+b, +Fl}:
      Bool.and(ex(Fl, v), Bool.and(nok(c, b, high(w)), cell(c, i)))
    case KAltM{+F1, +F2}:
      Bool.and(same(acc, F1), ex(F2, v))
    case KStarH{+a, +Vs, +i0}:
      Bool.and(Inv(c, a, i0, id, Vs, L, acc), nok(c, a, w))
    case KStarA{+a, +Vs, +i0}:
      Bool.and(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), v), nok(c, a, w)))
    case KStarK{+a, +Vs, +i0}:
      match v:
        case VNode{+q, +x}:
          Bool.and(Inv(c, a, i0, id, UCon{i, Vs}, L, pickc(is.asb(q), i, acc)), nok(c, a, w))
        case _:
          False{}
    case KRefM{}:
      Bool.and(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), v)))
    case KStore{}:
      Bool.and(cell(c, i), ex(E(c, rl(c, w), i), v))

law pst.call:
  for +c: Cx
  for +F: UL
  for +e: Nat
  for +addr: U32
  for +pos: U32
  for +tm: Tree<Entry>
  for -v0: V
  for h: Pst(c, F, go(e, SNode{}, addr, pos, 0, UNil{}, UNil{}, OO(c, tm, VNode{rdO(c, addr), rdA(c, addr)})))
  Pst(c, F, go(e, SNode{}, addr, pos, 0, UNil{}, UNil{}, call(OO(c, tm, v0), addr)))

def pst.call(c, F, e, addr, pos, tm, v0, h):
  %Equal.sym(Out, call(OO(c, tm, v0), addr), OO(c, tm, VNode{rdO(c, addr), rdA(c, addr)}), call.ok(c, tm, v0, addr)) : Pst(c, F, go(e, SNode{}, addr, pos, 0, UNil{}, UNil{}, _))
  h

# small facts used below

law ex.bad:
  for +c: Cx
  for +i: U32
  T(ex(E(c, Bad{}, i), VEnds{UNil{}}))

def ex.bad(c, i):
  %Equal.sym(UL, E(c, Bad{}, i), UNil{}, E.bad(c, suf(c, i), "", i)) : T(ex(_, VEnds{UNil{}}))
  {==}

law E.U1:
  for +c: Cx
  for +b: R
  for +y: U32
  T(same(E(c, b, y), U(c, b, UCon{y, UNil{}})))

def E.U1(c, b, y):
  same.i(E(c, b, y), uapp(E(c, b, y), UNil{}), sub.uapp.l(E(c, b, y), E(c, b, y), UNil{}, sub.refl(E(c, b, y))), uapp.sub(E(c, b, y), UNil{}, E(c, b, y), sub.refl(E(c, b, y)), {==}))

law same.nil.r:
  for +a: UL
  T(same(a, uapp(a, UNil{})))

def same.nil.r(a):
  same.i(a, uapp(a, UNil{}), sub.uapp.l(a, a, UNil{}, sub.refl(a)), uapp.sub(a, UNil{}, a, sub.refl(a), {==}))

law same.merge3:
  for +acc: UL
  for +r: UL
  for +X: UL
  for +Y: UL
  for +h: T(same(r, X))
  T(same(uapp(merge(acc, r), Y), uapp(acc, uapp(X, Y))))

def same.merge3(acc, r, X, Y, h):
  +hm = merge.same(acc, r)
  +sub1 = uapp.sub(merge(acc, r), Y, uapp(acc, uapp(X, Y)), sub.trans(merge(acc, r), uapp(acc, r), uapp(acc, uapp(X, Y)), same.l(merge(acc, r), uapp(acc, r), hm), uapp.sub(acc, r, uapp(acc, uapp(X, Y)), sub.uapp.l(acc, acc, uapp(X, Y), sub.refl(acc)), sub.uapp.r(r, acc, uapp(X, Y), sub.uapp.l(r, X, Y, same.l(r, X, h))))), sub.uapp.r(Y, acc, uapp(X, Y), sub.uapp.r(Y, X, Y, sub.refl(Y))))
  +sub2 = uapp.sub(acc, uapp(X, Y), uapp(merge(acc, r), Y), sub.uapp.l(acc, merge(acc, r), Y, sub.merge.l(acc, acc, r, sub.refl(acc))), uapp.sub(X, Y, uapp(merge(acc, r), Y), sub.uapp.l(X, merge(acc, r), Y, sub.merge.r(X, acc, r, same.r(r, X, h))), sub.uapp.r(Y, merge(acc, r), Y, sub.refl(Y))))
  same.i(uapp(merge(acc, r), Y), uapp(acc, uapp(X, Y)), sub1, sub2)

law same.merge2:
  for +acc: UL
  for +r: UL
  for +F1: UL
  for +F2: UL
  for +h1: T(same(acc, F1))
  for +h2: T(same(r, F2))
  T(same(merge(acc, r), uapp(F1, F2)))

def same.merge2(acc, r, F1, F2, h1, h2):
  +hm = merge.same(acc, r)
  same.i(merge(acc, r), uapp(F1, F2), sub.trans(merge(acc, r), uapp(acc, r), uapp(F1, F2), same.l(merge(acc, r), uapp(acc, r), hm), uapp.sub(acc, r, uapp(F1, F2), sub.uapp.l(acc, F1, F2, same.l(acc, F1, h1)), sub.uapp.r(r, F1, F2, same.l(r, F2, h2)))), uapp.sub(F1, F2, merge(acc, r), sub.merge.l(F1, acc, r, same.r(acc, F1, h1)), sub.merge.r(F2, acc, r, same.r(r, F2, h2))))

law cells.same:
  for +c: Cx
  for +a: UL
  for +b: UL
  for +hs: T(same(a, b))
  for +hb: T(cells(c, b))
  T(cells(c, a))

def cells.same(c, a, b, hs, hb):
  cells.sub(a, c, b, same.l(a, b, hs), hb)

law cells.fil:
  for +c: Cx
  for +id: U32
  for +F: UL
  for +hF: T(cells(c, F))
  T(cells(c, fil(c, id, F)))

def cells.fil(c, id, F, hF):
  cells.sub(fil(c, id, F), c, F, fil.self(fil(c, id, F), c, id, F, sub.refl(fil(c, id, F))), hF)

law cell.of.one:
  for +c: Cx
  for +y: U32
  for +F: UL
  for +hs: T(same(UCon{y, UNil{}}, F))
  for +hF: T(cells(c, F))
  T(cell(c, y))

def cell.of.one(c, y, F, hs, hF):
  cells.has(c, F, y, hF, sub.head(y, UNil{}, F, same.l(UCon{y, UNil{}}, F, hs)))

law ref.go.ex:
  for t: RT
  for +c: Cx
  for +n: String
  for +h: U32
  for +root: U32
  for +hR: T(rulesp(c, t))
  for +hr: T(ref.go(t, n, h, root))
  T(Bool.and(nok(c, body(cg2(c), rk(t, h)), root), String.eq(String.to_lower(rk(t, h)), String.to_lower(n))))

law ifs.eq.t:
  for b: Bool
  for -x: String
  for -y: String
  for +e: T(b)
  {ifs(b, x, y) == x : String}

def ifs.eq.t(b, x, y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      false.elim({ifs(False{}, x, y) == x : String}, e)

law ifs.eq.f:
  for b: Bool
  for -x: String
  for -y: String
  for +e: T(Bool.not(b))
  {ifs(b, x, y) == y : String}

def ifs.eq.f(b, x, y, e):
  match b:
    case True{}:
      false.elim({ifs(True{}, x, y) == y : String}, e)
    case False{}:
      {==}

law ref.hit:
  for +c: Cx
  for +k: String
  for +x: U32
  for +r: RT
  for +n: String
  for +h: U32
  for +root: U32
  for +hR: T(rulesp(c, RCon{k, x, r}))
  for +h1: T(Bool.and(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root))))
  T(Bool.and(nok(c, body(cg2(c), rk(RCon{k, x, r}, h)), root), String.eq(String.to_lower(rk(RCon{k, x, r}, h)), String.to_lower(n))))

law tr.nok:
  for +c: Cx
  for +r: R
  for +x: U32
  for +root: U32
  for +e: T(U32.is_eq(x, root))
  for +h: T(nok(c, r, x))
  T(nok(c, r, root))

def tr.nok(c, r, x, root, e, h):
  %u32.eq.t(x, root, e) : T(nok(c, r, _))
  h

def ref.hit(c, k, x, r, n, h, root, hR, h1):
  %Equal.sym(String, ifs(U32.is_eq(h, 0), k, rk(r, (h - 1 : U32))), k, ifs.eq.t(U32.is_eq(h, 0), k, rk(r, (h - 1 : U32)), and.l(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root)), h1))) : T(Bool.and(nok(c, body(cg2(c), _), root), String.eq(String.to_lower(_), String.to_lower(n))))
  and.i(nok(c, body(cg2(c), k), root), String.eq(String.to_lower(k), String.to_lower(n)), tr.nok(c, body(cg2(c), k), x, root, and.r(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root), and.r(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root)), h1)), and.l(nok(c, body(cg2(c), k), x), rulesp(c, r), hR)), and.l(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root), and.r(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root)), h1)))

law ref.miss:
  for +c: Cx
  for +k: String
  for +x: U32
  for +r: RT
  for +n: String
  for +h: U32
  for +root: U32
  for +rec: T(Bool.and(nok(c, body(cg2(c), rk(r, (h - 1 : U32))), root), String.eq(String.to_lower(rk(r, (h - 1 : U32))), String.to_lower(n))))
  for +ne: T(Bool.not(U32.is_eq(h, 0)))
  T(Bool.and(nok(c, body(cg2(c), rk(RCon{k, x, r}, h)), root), String.eq(String.to_lower(rk(RCon{k, x, r}, h)), String.to_lower(n))))

def ref.miss(c, k, x, r, n, h, root, rec, ne):
  %Equal.sym(String, ifs(U32.is_eq(h, 0), k, rk(r, (h - 1 : U32))), rk(r, (h - 1 : U32)), ifs.eq.f(U32.is_eq(h, 0), k, rk(r, (h - 1 : U32)), ne)) : T(Bool.and(nok(c, body(cg2(c), _), root), String.eq(String.to_lower(_), String.to_lower(n))))
  rec

def ref.go.ex(t, c, n, h, root, hR, hr):
  match t:
    case RNil{}:
      false.elim(T(Bool.and(nok(c, body(cg2(c), rk(RNil{}, h)), root), String.eq(String.to_lower(rk(RNil{}, h)), String.to_lower(n)))), hr)
    case RCon{+k, +x, +r}:
      or.c(Bool.and(U32.is_eq(h, 0), Bool.and(String.eq(String.to_lower(k), String.to_lower(n)), U32.is_eq(x, root))), Bool.and(Bool.not(U32.is_eq(h, 0)), ref.go(r, n, (h - 1 : U32), root)), T(Bool.and(nok(c, body(cg2(c), rk(RCon{k, x, r}, h)), root), String.eq(String.to_lower(rk(RCon{k, x, r}, h)), String.to_lower(n)))), hr, +h1 => ref.hit(c, k, x, r, n, h, root, hR, h1), +h2 => ref.miss(c, k, x, r, n, h, root, ref.go.ex(r, c, n, (h - 1 : U32), root, and.r(nok(c, body(cg2(c), k), x), rulesp(c, r), hR), and.r(Bool.not(U32.is_eq(h, 0)), ref.go(r, n, (h - 1 : U32), root), h2)), and.l(Bool.not(U32.is_eq(h, 0)), ref.go(r, n, (h - 1 : U32), root), h2)))

law scan.node:
  for +c: Cx
  for +tm: Tree<Entry>
  for +e: Nat
  for +z: R
  for +id: U32
  for +i: U32
  for +tb: U32
  for +hm: T(mok(c, tm))
  for +hv: T(clso(c, z, tb))
  for +ga: T(Glob(c))
  for +hc: T(cell(c, i))
  Pst(c, fil(c, id, E(c, Star{z}, i)), scan.o(uO(c), unshadow(Entry, tm), scanf(e, tb, id, i, UNil{}, step(uA(c), tb, id, i))))

def scan.node(c, tm, e, z, id, i, tb, hm, hv, ga, hc):
  %Equal.sym(Array<U32> & F, step(uA(c), tb, id, i), (uA(c), F{kept(c, id, i), cmatch(z, rdA(c, i))}), step.ok(c, z, tb, id, i, hv)) : Pst(c, fil(c, id, E(c, Star{z}, i)), scan.o(uO(c), unshadow(Entry, tm), scanf(e, tb, id, i, UNil{}, _)))
  scan.pst(c, tm, fil(c, id, E(c, Star{z}, i)), scanf(e, tb, id, i, UNil{}, (uA(c), F{kept(c, id, i), cmatch(z, rdA(c, i))})), hm, scanf.ok(e, c, z, i, tb, id, UNil{}, i, UNil{}, kept(c, id, i), cmatch(z, rdA(c, i)), ga, hv, inv.init(c, z, i, id, hc), {==}, {==}))

law badr.eq:
  for r: R
  for +h: T(badr(r))
  {r == Bad{} : R}

def badr.eq(r, h):
  match r:
    case Bad{}:
      {==}
    case Emp{}:
      false.elim({Emp{} == Bad{} : R}, h)
    case Lit{+x}:
      false.elim({Lit{x} == Bad{} : R}, h)
    case Rng{+x, +y}:
      false.elim({Rng{x, y} == Bad{} : R}, h)
    case Cat{+x, +y}:
      false.elim({Cat{x, y} == Bad{} : R}, h)
    case Alt{+x, +y}:
      false.elim({Alt{x, y} == Bad{} : R}, h)
    case Star{+x}:
      false.elim({Star{x} == Bad{} : R}, h)
    case Ref{+n}:
      false.elim({Ref{n} == Bad{} : R}, h)

law ref.bad.k:
  for +c: Cx
  for +n: String
  for +i: U32
  for +hb: T(badr(lk(cg2(c), n)))
  T(same(UNil{}, E(c, body(cg2(c), n), i)))

def ref.bad.k(c, n, i, hb):
  %Equal.sym(R, lk(cg2(c), n), Bad{}, badr.eq(lk(cg2(c), n), hb)) : T(same(UNil{}, E(c, simp0(_), i)))
  %Equal.sym(UL, E(c, Bad{}, i), UNil{}, E.bad(c, suf(c, i), "", i)) : T(same(UNil{}, _))
  {==}

law ref.bad:
  for +c: Cx
  for +n: String
  for +i: U32
  for +hc: T(cell(c, i))
  for +hb: T(badr(lk(cg2(c), n)))
  T(same(UNil{}, E(c, Ref{n}, i)))

def ref.bad(c, n, i, hc, hb):
  same.trans(UNil{}, E(c, body(cg2(c), n), i), E(c, Ref{n}, i), ref.bad.k(c, n, i, hb), E.ref.same(c, n, n, i, hc, str.refl(String.to_lower(n))))

law go.ok:
  for +c: Cx
  for +f: Nat
  for +k: K
  for +id: U32
  for +i: U32
  for +w: U32
  for +L: UL
  for +acc: UL
  for +tm: Tree<Entry>
  for +v: V
  for +ga: T(Glob(c))
  for +hR: T(rulesp(c, crt(c)))
  for +hm: T(mok(c, tm))
  for +hp: T(pre(c, k, id, i, w, L, acc, v))
  Pst(c, tgt(c, k, id, i, w, L, acc), go(f, st.of(k), id, i, w, L, acc, OO(c, tm, v)))

def go.ok(c, f, k, id, i, w, L, acc, tm, v, ga, hR, hm, hp):
  match f:
    case 0n:
      (tm, VStuck{}, {==}, hm, {==})
    case 1n+e:
      match k:
        case KNode{+r}:
          match r:
            case Emp{}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      (tm, VOne{i}, {==}, hm, E.emp.go(c, suf(c, i), i))
                    case OBad{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Emp{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Emp{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Bad{}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      (tm, VEnds{UNil{}}, {==}, hm, ex.bad(c, i))
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Bad{}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Bad{}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Lit{+h}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      (tm, single(U32.is_eq(x, rdA(c, i)), i), lit.do.ok(c, tm, x, i), hm, leaf.ex(c, Lit{h}, i, U32.is_eq(x, rdA(c, i)), Equal.cong(U32, Bool, t9 => U32.is_eq(t9, rdA(c, i)), x, Char.to_u32(h), u32.eq.t(x, Char.to_u32(h), and.l(U32.is_eq(x, Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)), and.l(nok.at(c, Lit{h}, OLit{}, x, id), cell(c, i), hp)))), {==}, and.r(U32.is_eq(x, Char.to_u32(h)), Bool.not(U32.is_eq(Char.to_u32(h), 4294967295)), and.l(nok.at(c, Lit{h}, OLit{}, x, id), cell(c, i), hp)), ga, and.r(nok.at(c, Lit{h}, OLit{}, x, id), cell(c, i), hp)))
                    case OCls{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Lit{h}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Lit{h}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Rng{+lo, +hi}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      (tm, single(cmatch(Rng{lo, hi}, rdA(c, i)), i), cls.do.ok(c, tm, Rng{lo, hi}, x, i, and.l(nok.at(c, Rng{lo, hi}, OCls{}, x, id), cell(c, i), hp)), hm, leaf.ex(c, Rng{lo, hi}, i, cmatch(Rng{lo, hi}, rdA(c, i)), {==}, clso.leafy(c, Rng{lo, hi}, x, and.l(nok.at(c, Rng{lo, hi}, OCls{}, x, id), cell(c, i), hp)), clso.nend(c, Rng{lo, hi}, x, and.l(nok.at(c, Rng{lo, hi}, OCls{}, x, id), cell(c, i), hp)), ga, and.r(nok.at(c, Rng{lo, hi}, OCls{}, x, id), cell(c, i), hp)))
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Rng{lo, hi}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Rng{lo, hi}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Cat{a1, +y}:
              match a1:
                case Star{+z}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Star{z}, i)), E(c, Cat{Star{z}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Star{z}, y, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Star{z}, i), U(c, y, E(c, Star{z}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Star{z}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Star{z}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Star{z}, low(x)), cell(c, i), and.l(nok(c, Star{z}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Star{z}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Star{z}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Star{z}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Star{z}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Star{z}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Star{z}, i)), and.r(nok(c, Star{z}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Star{z}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Star{z}, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          pst.conv(c, U(c, y, fil(c, id, E(c, Star{z}, i))), E(c, Cat{Star{z}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SStarH{}, id, i, low(x), UCon{i, UNil{}}, UNil{}, OO(c, tm, VNone{}))), same.trans(U(c, y, fil(c, id, E(c, Star{z}, i))), U(c, y, E(c, Star{z}, i)), E(c, Cat{Star{z}, y}, i), U.fil.same(c, y, id, E(c, Star{z}, i), ga, E.cells(c, Star{z}, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp)), and.r(nok(c, y, high(x)), ckm(c, KBit{}, y, id), and.r(nok(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp)))), cat.same(c, Star{z}, y, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp))), pst.bind(c, fil(c, id, E(c, Star{z}, i)), U(c, y, fil(c, id, E(c, Star{z}, i))), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SStarH{}, id, i, low(x), UCon{i, UNil{}}, UNil{}, OO(c, tm, VNone{})), go.ok(c, e, KStarH{z, UNil{}, i}, id, i, low(x), UCon{i, UNil{}}, UNil{}, tm, VNone{}, ga, hR, hm, and.i(Inv(c, z, i, id, UNil{}, UCon{i, UNil{}}, UNil{}), nok(c, z, low(x)), inv.init(c, z, i, id, and.r(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp)), and.l(nok(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, fil(c, id, E(c, Star{z}, i))}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(fil(c, id, E(c, Star{z}, i)), v2), Bool.and(nok(c, y, high(x)), cells(c, fil(c, id, E(c, Star{z}, i)))), hv2, and.i(nok(c, y, high(x)), cells(c, fil(c, id, E(c, Star{z}, i))), and.l(nok(c, y, high(x)), ckm(c, KBit{}, y, id), and.r(nok(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp))), cells.fil(c, id, E(c, Star{z}, i), E.cells(c, Star{z}, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatS{}, x, id), cell(c, i), hp))))))))
                        case OCatSC{}:
                          pst.conv(c, U(c, y, fil(c, id, E(c, Star{z}, i))), E(c, Cat{Star{z}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, scan.o(uO(c), unshadow(Entry, tm), scanf(e, low(x), id, i, UNil{}, step(uA(c), low(x), id, i)))), same.trans(U(c, y, fil(c, id, E(c, Star{z}, i))), U(c, y, E(c, Star{z}, i)), E(c, Cat{Star{z}, y}, i), U.fil.same(c, y, id, E(c, Star{z}, i), ga, E.cells(c, Star{z}, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp)), and.r(nok(c, y, high(x)), ckm(c, KBit{}, y, id), and.r(clso(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp)))), cat.same(c, Star{z}, y, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp))), pst.bind(c, fil(c, id, E(c, Star{z}, i)), U(c, y, fil(c, id, E(c, Star{z}, i))), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), scan.o(uO(c), unshadow(Entry, tm), scanf(e, low(x), id, i, UNil{}, step(uA(c), low(x), id, i))), scan.node(c, tm, e, z, id, i, low(x), hm, and.l(clso(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp)), ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp)), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, fil(c, id, E(c, Star{z}, i))}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(fil(c, id, E(c, Star{z}, i)), v2), Bool.and(nok(c, y, high(x)), cells(c, fil(c, id, E(c, Star{z}, i)))), hv2, and.i(nok(c, y, high(x)), cells(c, fil(c, id, E(c, Star{z}, i))), and.l(nok(c, y, high(x)), ckm(c, KBit{}, y, id), and.r(clso(c, z, low(x)), Bool.and(nok(c, y, high(x)), ckm(c, KBit{}, y, id)), and.l(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp))), cells.fil(c, id, E(c, Star{z}, i), E.cells(c, Star{z}, i, ga, and.r(nok.at(c, Cat{Star{z}, y}, OCatSC{}, x, id), cell(c, i), hp))))))))
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Star{z}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Star{z}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Emp{}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Emp{}, i)), E(c, Cat{Emp{}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Emp{}, y, i, ga, and.r(nok.at(c, Cat{Emp{}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Emp{}, i), U(c, y, E(c, Emp{}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Emp{}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Emp{}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Emp{}, low(x)), cell(c, i), and.l(nok(c, Emp{}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Emp{}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Emp{}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Emp{}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Emp{}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Emp{}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Emp{}, i)), and.r(nok(c, Emp{}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Emp{}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Emp{}, i, ga, and.r(nok.at(c, Cat{Emp{}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Emp{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Emp{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Bad{}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Bad{}, i)), E(c, Cat{Bad{}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Bad{}, y, i, ga, and.r(nok.at(c, Cat{Bad{}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Bad{}, i), U(c, y, E(c, Bad{}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Bad{}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Bad{}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Bad{}, low(x)), cell(c, i), and.l(nok(c, Bad{}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Bad{}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Bad{}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Bad{}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Bad{}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Bad{}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Bad{}, i)), and.r(nok(c, Bad{}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Bad{}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Bad{}, i, ga, and.r(nok.at(c, Cat{Bad{}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Bad{}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Bad{}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Lit{+c0}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Lit{c0}, i)), E(c, Cat{Lit{c0}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Lit{c0}, y, i, ga, and.r(nok.at(c, Cat{Lit{c0}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Lit{c0}, i), U(c, y, E(c, Lit{c0}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Lit{c0}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Lit{c0}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Lit{c0}, low(x)), cell(c, i), and.l(nok(c, Lit{c0}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Lit{c0}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Lit{c0}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Lit{c0}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Lit{c0}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Lit{c0}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Lit{c0}, i)), and.r(nok(c, Lit{c0}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Lit{c0}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Lit{c0}, i, ga, and.r(nok.at(c, Cat{Lit{c0}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Lit{c0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Lit{c0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Rng{+p0, +p1}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Rng{p0, p1}, i)), E(c, Cat{Rng{p0, p1}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Rng{p0, p1}, y, i, ga, and.r(nok.at(c, Cat{Rng{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Rng{p0, p1}, i), U(c, y, E(c, Rng{p0, p1}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Rng{p0, p1}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Rng{p0, p1}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Rng{p0, p1}, low(x)), cell(c, i), and.l(nok(c, Rng{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Rng{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Rng{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Rng{p0, p1}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Rng{p0, p1}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Rng{p0, p1}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Rng{p0, p1}, i)), and.r(nok(c, Rng{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Rng{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Rng{p0, p1}, i, ga, and.r(nok.at(c, Cat{Rng{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Rng{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Rng{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Cat{+p0, +p1}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Cat{p0, p1}, i)), E(c, Cat{Cat{p0, p1}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Cat{p0, p1}, y, i, ga, and.r(nok.at(c, Cat{Cat{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Cat{p0, p1}, i), U(c, y, E(c, Cat{p0, p1}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Cat{p0, p1}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Cat{p0, p1}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Cat{p0, p1}, low(x)), cell(c, i), and.l(nok(c, Cat{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Cat{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Cat{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Cat{p0, p1}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Cat{p0, p1}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Cat{p0, p1}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Cat{p0, p1}, i)), and.r(nok(c, Cat{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Cat{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Cat{p0, p1}, i, ga, and.r(nok.at(c, Cat{Cat{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Cat{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Cat{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Alt{+p0, +p1}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Alt{p0, p1}, i)), E(c, Cat{Alt{p0, p1}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Alt{p0, p1}, y, i, ga, and.r(nok.at(c, Cat{Alt{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Alt{p0, p1}, i), U(c, y, E(c, Alt{p0, p1}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Alt{p0, p1}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Alt{p0, p1}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Alt{p0, p1}, low(x)), cell(c, i), and.l(nok(c, Alt{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Alt{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Alt{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Alt{p0, p1}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Alt{p0, p1}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Alt{p0, p1}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Alt{p0, p1}, i)), and.r(nok(c, Alt{p0, p1}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Alt{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Alt{p0, p1}, i, ga, and.r(nok.at(c, Cat{Alt{p0, p1}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Alt{p0, p1}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Alt{p0, p1}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
                case Ref{+p0}:
                  match v:
                    case VNone{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                    case VStuck{}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                    case VEnds{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                    case VOne{+x9}:
                      false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                    case VNode{+q, +x}:
                      match q:
                        case OLit{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                        case OCls{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                        case OAlt{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                        case OCat{}:
                          pst.conv(c, U(c, y, E(c, Ref{p0}, i)), E(c, Cat{Ref{p0}, y}, i), go(e, SCat{}, id, i, x, UNil{}, UNil{}, go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x)))), cat.same(c, Ref{p0}, y, i, ga, and.r(nok.at(c, Cat{Ref{p0}, y}, OCat{}, x, id), cell(c, i), hp)), pst.bind(c, E(c, Ref{p0}, i), U(c, y, E(c, Ref{p0}, i)), o => go(e, SCat{}, id, i, x, UNil{}, UNil{}, o), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), pst.call(c, E(c, Ref{p0}, i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{Ref{p0}}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, Ref{p0}, low(x)), cell(c, i), and.l(nok(c, Ref{p0}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Ref{p0}, y}, OCat{}, x, id), cell(c, i), hp)), and.r(nok.at(c, Cat{Ref{p0}, y}, OCat{}, x, id), cell(c, i), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCat{y, E(c, Ref{p0}, i)}, id, i, x, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, Ref{p0}, i), v2), Bool.and(nok(c, y, high(x)), cells(c, E(c, Ref{p0}, i))), hv2, and.i(nok(c, y, high(x)), cells(c, E(c, Ref{p0}, i)), and.r(nok(c, Ref{p0}, low(x)), nok(c, y, high(x)), and.l(nok.at(c, Cat{Ref{p0}, y}, OCat{}, x, id), cell(c, i), hp)), E.cells(c, Ref{p0}, i, ga, and.r(nok.at(c, Cat{Ref{p0}, y}, OCat{}, x, id), cell(c, i), hp)))))))
                        case OCatS{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                        case OCatSC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                        case OStar{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                        case OStarC{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                        case ORefM{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                        case ORef{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                        case OEmp{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                        case OBad{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                        case ASelB{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                        case ASelL{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                        case ASelR{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                        case ASelN{}:
                          false.elim(Pst(c, tgt(c, KNode{Cat{Ref{p0}, y}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Cat{Ref{p0}, y}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Alt{+a1, +b2}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      (tm, single(cmatch(Alt{a1, b2}, rdA(c, i)), i), cls.do.ok(c, tm, Alt{a1, b2}, x, i, and.l(nok.at(c, Alt{a1, b2}, OCls{}, x, id), cell(c, i), hp)), hm, leaf.ex(c, Alt{a1, b2}, i, cmatch(Alt{a1, b2}, rdA(c, i)), {==}, clso.leafy(c, Alt{a1, b2}, x, and.l(nok.at(c, Alt{a1, b2}, OCls{}, x, id), cell(c, i), hp)), clso.nend(c, Alt{a1, b2}, x, and.l(nok.at(c, Alt{a1, b2}, OCls{}, x, id), cell(c, i), hp)), ga, and.r(nok.at(c, Alt{a1, b2}, OCls{}, x, id), cell(c, i), hp)))
                    case OAlt{}:
                      %Equal.sym(Out, alt.sel(uO(c), uA(c), unshadow(Entry, tm), id, i), OO(c, tm, altv(c, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))), alt.sel.ok(c, tm, id, i)) : Pst(c, E(c, Alt{a1, b2}, i), go(e, SAlt{}, id, i, x, UNil{}, UNil{}, _))
                      go.ok(c, e, KAlt{a1, b2}, id, i, x, UNil{}, UNil{}, tm, altv(c, U32.is_ge(rdA(c, i), 128), id, rdA(c, i)), ga, hR, hm, and.i(altpre(c, a1, b2, rdA(c, i), altv(c, U32.is_ge(rdA(c, i), 128), id, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a1, low(x)), nok(c, b2, high(x)))), altpre.ok(U32.is_ge(rdA(c, i), 128), c, a1, b2, id, rdA(c, i), {==}, and.l(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id), and.r(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id)), and.r(nok(c, a1, low(x)), Bool.and(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))), and.l(nok.at(c, Alt{a1, b2}, OAlt{}, x, id), cell(c, i), hp)))), and.r(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id), and.r(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id)), and.r(nok(c, a1, low(x)), Bool.and(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))), and.l(nok.at(c, Alt{a1, b2}, OAlt{}, x, id), cell(c, i), hp))))), and.i(cell(c, i), Bool.and(nok(c, a1, low(x)), nok(c, b2, high(x))), and.r(nok.at(c, Alt{a1, b2}, OAlt{}, x, id), cell(c, i), hp), and.i(nok(c, a1, low(x)), nok(c, b2, high(x)), and.l(nok(c, a1, low(x)), Bool.and(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))), and.l(nok.at(c, Alt{a1, b2}, OAlt{}, x, id), cell(c, i), hp)), and.l(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id)), and.r(nok(c, a1, low(x)), Bool.and(nok(c, b2, high(x)), Bool.and(ckm(c, KL{}, a1, id), ckm(c, KR{}, b2, id))), and.l(nok.at(c, Alt{a1, b2}, OAlt{}, x, id), cell(c, i), hp)))))))
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Alt{a1, b2}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Alt{a1, b2}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Star{+a1}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      pst.conv(c, fil(c, id, E(c, Star{a1}, i)), E(c, Star{a1}, i), go(e, SStarH{}, id, i, x, UCon{i, UNil{}}, UNil{}, OO(c, tm, VNone{})), fil.one.same(c, id, E(c, Star{a1}, i), and.r(nok(c, a1, x), all128(c, POne{id}, 128n, 0), and.l(nok.at(c, Star{a1}, OStar{}, x, id), cell(c, i), hp))), go.ok(c, e, KStarH{a1, UNil{}, i}, id, i, x, UCon{i, UNil{}}, UNil{}, tm, VNone{}, ga, hR, hm, and.i(Inv(c, a1, i, id, UNil{}, UCon{i, UNil{}}, UNil{}), nok(c, a1, x), inv.init(c, a1, i, id, and.r(nok.at(c, Star{a1}, OStar{}, x, id), cell(c, i), hp)), and.l(nok(c, a1, x), all128(c, POne{id}, 128n, 0), and.l(nok.at(c, Star{a1}, OStar{}, x, id), cell(c, i), hp)))))
                    case OStarC{}:
                      pst.conv(c, fil(c, id, E(c, Star{a1}, i)), E(c, Star{a1}, i), scan.o(uO(c), unshadow(Entry, tm), scanf(e, x, id, i, UNil{}, step(uA(c), x, id, i))), fil.one.same(c, id, E(c, Star{a1}, i), and.r(clso(c, a1, x), all128(c, POne{id}, 128n, 0), and.l(nok.at(c, Star{a1}, OStarC{}, x, id), cell(c, i), hp))), scan.node(c, tm, e, a1, id, i, x, hm, and.l(clso(c, a1, x), all128(c, POne{id}, 128n, 0), and.l(nok.at(c, Star{a1}, OStarC{}, x, id), cell(c, i), hp)), ga, and.r(nok.at(c, Star{a1}, OStarC{}, x, id), cell(c, i), hp)))
                    case ORefM{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ORefM{}, x}))), hp)
                    case ORef{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ORef{}, x}))), hp)
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{OBad{}, x}))), hp)
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Star{a1}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Star{a1}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
            case Ref{+n}:
              match v:
                case VNone{}:
                  false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
                case VStuck{}:
                  false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
                case VEnds{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
                case VOne{+x9}:
                  false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
                case VNode{+q, +x}:
                  match q:
                    case OLit{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OLit{}, x}))), hp)
                    case OCls{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OCls{}, x}))), hp)
                    case OAlt{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OAlt{}, x}))), hp)
                    case OCat{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OCat{}, x}))), hp)
                    case OCatS{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OCatS{}, x}))), hp)
                    case OCatSC{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OCatSC{}, x}))), hp)
                    case OStar{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OStar{}, x}))), hp)
                    case OStarC{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OStarC{}, x}))), hp)
                    case ORefM{}:
                      %Equal.sym(Out, probe(uO(c), uA(c), unshadow(Entry, tm), i, x), OO(c, tm, probe.v(tr.rd(Entry, tm, hash(i, x)), i, x)), probe.ok(c, tm, i, x)) : Pst(c, E(c, Ref{n}, i), go(e, SRefM{}, id, i, x, UNil{}, UNil{}, _))
                      pst.conv(c, E(c, rl(c, x), i), E(c, Ref{n}, i), go(e, SRefM{}, id, i, x, UNil{}, UNil{}, OO(c, tm, probe.v(tr.rd(Entry, tm, hash(i, x)), i, x))), E.ref.same(c, rk(crt(c), high(x)), n, i, and.r(nok.at(c, Ref{n}, ORefM{}, x, id), cell(c, i), hp), and.r(nok(c, body(cg2(c), rk(crt(c), high(x))), low(x)), String.eq(String.to_lower(rk(crt(c), high(x))), String.to_lower(n)), ref.go.ex(crt(c), c, n, high(x), low(x), hR, and.l(nok.at(c, Ref{n}, ORefM{}, x, id), cell(c, i), hp)))), go.ok(c, e, KRefM{}, id, i, x, UNil{}, UNil{}, tm, probe.v(tr.rd(Entry, tm, hash(i, x)), i, x), ga, hR, hm, and.i(cell(c, i), Bool.and(nok(c, rl(c, x), low(x)), mst(E(c, rl(c, x), i), probe.v(tr.rd(Entry, tm, hash(i, x)), i, x))), and.r(nok.at(c, Ref{n}, ORefM{}, x, id), cell(c, i), hp), and.i(nok(c, rl(c, x), low(x)), mst(E(c, rl(c, x), i), probe.v(tr.rd(Entry, tm, hash(i, x)), i, x)), and.l(nok(c, body(cg2(c), rk(crt(c), high(x))), low(x)), String.eq(String.to_lower(rk(crt(c), high(x))), String.to_lower(n)), ref.go.ex(crt(c), c, n, high(x), low(x), hR, and.l(nok.at(c, Ref{n}, ORefM{}, x, id), cell(c, i), hp))), probe.memo(c, tr.rd(Entry, tm, hash(i, x)), i, x, get.ent(c, tm, hash(i, x), hm))))))
                    case ORef{}:
                      pst.conv(c, E(c, rl(c, x), i), E(c, Ref{n}, i), go(e, SNode{}, low(x), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(x))), E.ref.same(c, rk(crt(c), high(x)), n, i, and.r(nok.at(c, Ref{n}, ORef{}, x, id), cell(c, i), hp), and.r(nok(c, body(cg2(c), rk(crt(c), high(x))), low(x)), String.eq(String.to_lower(rk(crt(c), high(x))), String.to_lower(n)), ref.go.ex(crt(c), c, n, high(x), low(x), hR, and.l(nok.at(c, Ref{n}, ORef{}, x, id), cell(c, i), hp)))), pst.call(c, E(c, rl(c, x), i), e, low(x), i, tm, VNone{}, go.ok(c, e, KNode{rl(c, x)}, low(x), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(x)), rdA(c, low(x))}, ga, hR, hm, and.i(nok(c, rl(c, x), low(x)), cell(c, i), and.l(nok(c, body(cg2(c), rk(crt(c), high(x))), low(x)), String.eq(String.to_lower(rk(crt(c), high(x))), String.to_lower(n)), ref.go.ex(crt(c), c, n, high(x), low(x), hR, and.l(nok.at(c, Ref{n}, ORef{}, x, id), cell(c, i), hp))), and.r(nok.at(c, Ref{n}, ORef{}, x, id), cell(c, i), hp)))))
                    case OEmp{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{OEmp{}, x}))), hp)
                    case OBad{}:
                      (tm, VEnds{UNil{}}, {==}, hm, ref.bad(c, n, i, and.r(nok.at(c, Ref{n}, OBad{}, x, id), cell(c, i), hp), and.l(nok.at(c, Ref{n}, OBad{}, x, id), cell(c, i), hp)))
                    case ASelB{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{ASelB{}, x}))), hp)
                    case ASelL{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{ASelL{}, x}))), hp)
                    case ASelR{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{ASelR{}, x}))), hp)
                    case ASelN{}:
                      false.elim(Pst(c, tgt(c, KNode{Ref{n}}, id, i, w, L, acc), go(1n+e, st.of(KNode{Ref{n}}), id, i, w, L, acc, OO(c, tm, VNode{ASelN{}, x}))), hp)
        case KCat{+b, +Fl}:
          match v:
            case VNone{}:
              false.elim(Pst(c, tgt(c, KCat{b, Fl}, id, i, w, L, acc), go(1n+e, st.of(KCat{b, Fl}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              match r:
                case UNil{}:
                  (tm, VEnds{UNil{}}, {==}, hm, U.same(c, b, UNil{}, Fl, and.l(ex(Fl, VEnds{UNil{}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)))
                case UCon{+y, +t}:
                  match t:
                    case UNil{}:
                      pst.conv(c, E(c, b, y), U(c, b, Fl), go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), high(w))), same.trans(E(c, b, y), U(c, b, UCon{y, UNil{}}), U(c, b, Fl), E.U1(c, b, y), U.same(c, b, UCon{y, UNil{}}, Fl, and.l(ex(Fl, VEnds{UCon{y, UNil{}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp))), pst.call(c, E(c, b, y), e, high(w), y, tm, VNone{}, go.ok(c, e, KNode{b}, high(w), y, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, y), and.l(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VEnds{UCon{y, UNil{}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)), cell.of.one(c, y, Fl, and.l(ex(Fl, VEnds{UCon{y, UNil{}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp), and.r(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VEnds{UCon{y, UNil{}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)))))))
                    case UCon{+y2, +t2}:
                      pst.conv(c, U(c, b, UCon{y, UCon{y2, t2}}), U(c, b, Fl), go(e, SCatL{}, id, i, w, UCon{y, UCon{y2, t2}}, UNil{}, OO(c, tm, VNone{})), U.same(c, b, UCon{y, UCon{y2, t2}}, Fl, and.l(ex(Fl, VEnds{UCon{y, UCon{y2, t2}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)), go.ok(c, e, KCatL{b}, id, i, w, UCon{y, UCon{y2, t2}}, UNil{}, tm, VNone{}, ga, hR, hm, and.i(cells(c, UCon{y, UCon{y2, t2}}), nok(c, b, high(w)), cells.same(c, UCon{y, UCon{y2, t2}}, Fl, and.l(ex(Fl, VEnds{UCon{y, UCon{y2, t2}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp), and.r(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VEnds{UCon{y, UCon{y2, t2}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp))), and.l(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VEnds{UCon{y, UCon{y2, t2}}}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)))))
            case VOne{+y}:
              pst.conv(c, E(c, b, y), U(c, b, Fl), go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), high(w))), same.trans(E(c, b, y), U(c, b, UCon{y, UNil{}}), U(c, b, Fl), E.U1(c, b, y), U.same(c, b, UCon{y, UNil{}}, Fl, and.l(ex(Fl, VOne{y}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp))), pst.call(c, E(c, b, y), e, high(w), y, tm, VNone{}, go.ok(c, e, KNode{b}, high(w), y, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, y), and.l(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VOne{y}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)), cell.of.one(c, y, Fl, and.l(ex(Fl, VOne{y}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp), and.r(nok(c, b, high(w)), cells(c, Fl), and.r(ex(Fl, VOne{y}), Bool.and(nok(c, b, high(w)), cells(c, Fl)), hp)))))))
            case VNode{+q, +x}:
              false.elim(Pst(c, tgt(c, KCat{b, Fl}, id, i, w, L, acc), go(1n+e, st.of(KCat{b, Fl}), id, i, w, L, acc, OO(c, tm, VNode{q, x}))), hp)
        case KCatL{+b}:
          match L:
            case UNil{}:
              (tm, vnorm(acc), {==}, hm, ex.vnorm(acc, uapp(acc, UNil{}), same.nil.r(acc)))
            case UCon{+y, +t}:
              pst.bind(c, E(c, b, y), uapp(acc, uapp(E(c, b, y), U(c, b, t))), o => go(e, SCatA{}, id, i, w, t, acc, o), go(e, SNode{}, high(w), y, 0, UNil{}, UNil{}, call(OO(c, tm, v), high(w))), pst.call(c, E(c, b, y), e, high(w), y, tm, v, go.ok(c, e, KNode{b}, high(w), y, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, y), and.r(cells(c, UCon{y, t}), nok(c, b, high(w)), hp), and.l(cell(c, y), cells(c, t), and.l(cells(c, UCon{y, t}), nok(c, b, high(w)), hp))))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KCatA{b, y}, id, i, w, t, acc, tm2, v2, ga, hR, hm2, and.i(ex(E(c, b, y), v2), Bool.and(cells(c, t), nok(c, b, high(w))), hv2, and.i(cells(c, t), nok(c, b, high(w)), and.r(cell(c, y), cells(c, t), and.l(cells(c, UCon{y, t}), nok(c, b, high(w)), hp)), and.r(cells(c, UCon{y, t}), nok(c, b, high(w)), hp)))))
        case KCatA{+b, +y}:
          match v:
            case VNone{}:
              false.elim(Pst(c, tgt(c, KCatA{b, y}, id, i, w, L, acc), go(1n+e, st.of(KCatA{b, y}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              pst.conv(c, uapp(merge(acc, r), U(c, b, L)), uapp(acc, uapp(E(c, b, y), U(c, b, L))), go(e, SCatL{}, id, i, w, L, merge(acc, r), OO(c, tm, VNone{})), same.merge3(acc, r, E(c, b, y), U(c, b, L), and.l(ex(E(c, b, y), VEnds{r}), Bool.and(cells(c, L), nok(c, b, high(w))), hp)), go.ok(c, e, KCatL{b}, id, i, w, L, merge(acc, r), tm, VNone{}, ga, hR, hm, and.r(ex(E(c, b, y), VEnds{r}), Bool.and(cells(c, L), nok(c, b, high(w))), hp)))
            case VOne{+x}:
              pst.conv(c, uapp(merge(acc, UCon{x, UNil{}}), U(c, b, L)), uapp(acc, uapp(E(c, b, y), U(c, b, L))), go(e, SCatL{}, id, i, w, L, merge(acc, UCon{x, UNil{}}), OO(c, tm, VNone{})), same.merge3(acc, UCon{x, UNil{}}, E(c, b, y), U(c, b, L), and.l(ex(E(c, b, y), VOne{x}), Bool.and(cells(c, L), nok(c, b, high(w))), hp)), go.ok(c, e, KCatL{b}, id, i, w, L, merge(acc, UCon{x, UNil{}}), tm, VNone{}, ga, hR, hm, and.r(ex(E(c, b, y), VOne{x}), Bool.and(cells(c, L), nok(c, b, high(w))), hp)))
            case VNode{+q, +x}:
              false.elim(Pst(c, tgt(c, KCatA{b, y}, id, i, w, L, acc), go(1n+e, st.of(KCatA{b, y}), id, i, w, L, acc, OO(c, tm, VNode{q, x}))), hp)
        case KAlt{+a, +b}:
          match v:
            case VNone{}:
              false.elim(Pst(c, tgt(c, KAlt{a, b}, id, i, w, L, acc), go(1n+e, st.of(KAlt{a, b}), id, i, w, L, acc, OO(c, tm, VNone{}))), hp)
            case VStuck{}:
              false.elim(Pst(c, tgt(c, KAlt{a, b}, id, i, w, L, acc), go(1n+e, st.of(KAlt{a, b}), id, i, w, L, acc, OO(c, tm, VStuck{}))), hp)
            case VEnds{+x9}:
              false.elim(Pst(c, tgt(c, KAlt{a, b}, id, i, w, L, acc), go(1n+e, st.of(KAlt{a, b}), id, i, w, L, acc, OO(c, tm, VEnds{x9}))), hp)
            case VOne{+x9}:
              false.elim(Pst(c, tgt(c, KAlt{a, b}, id, i, w, L, acc), go(1n+e, st.of(KAlt{a, b}), id, i, w, L, acc, OO(c, tm, VOne{x9}))), hp)
            case VNode{+q, +x2}:
              match q:
                case OLit{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OCls{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OAlt{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OCat{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OCatS{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OCatSC{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OStar{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OStarC{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case ORefM{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case ORef{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OEmp{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case OBad{}:
                  (tm, VStuck{}, {==}, hm, {==})
                case ASelB{}:
                  pst.conv(c, uapp(E(c, a, i), E(c, b, i)), E(c, Alt{a, b}, i), go(e, SAltR{}, id, i, w, UNil{}, UNil{}, go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(w)))), alt.same(c, a, b, i), pst.bind(c, E(c, a, i), uapp(E(c, a, i), E(c, b, i)), o => go(e, SAltR{}, id, i, w, UNil{}, UNil{}, o), go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(w))), pst.call(c, E(c, a, i), e, low(w), i, tm, VNone{}, go.ok(c, e, KNode{a}, low(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(w)), rdA(c, low(w))}, ga, hR, hm, and.i(nok(c, a, low(w)), cell(c, i), and.l(nok(c, a, low(w)), nok(c, b, high(w)), and.r(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelB{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))), and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelB{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KAltR{b, E(c, a, i)}, id, i, w, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(ex(E(c, a, i), v2), Bool.and(nok(c, b, high(w)), cell(c, i)), hv2, and.i(nok(c, b, high(w)), cell(c, i), and.r(nok(c, a, low(w)), nok(c, b, high(w)), and.r(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelB{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))), and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelB{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)))))))
                case ASelL{}:
                  pst.conv(c, E(c, a, i), E(c, Alt{a, b}, i), go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(w))), alt.l.same(c, a, b, i, none.E(c, b, i, and.l(selq(ASelL{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp), ga, and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelL{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)))), pst.call(c, E(c, a, i), e, low(w), i, tm, VNone{}, go.ok(c, e, KNode{a}, low(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(w)), rdA(c, low(w))}, ga, hR, hm, and.i(nok(c, a, low(w)), cell(c, i), and.l(nok(c, a, low(w)), nok(c, b, high(w)), and.r(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelL{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))), and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelL{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))))))
                case ASelR{}:
                  pst.conv(c, E(c, b, i), E(c, Alt{a, b}, i), go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), high(w))), alt.r.same(c, a, b, i, none.E(c, a, i, and.l(selq(ASelR{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp), ga, and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelR{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)))), pst.call(c, E(c, b, i), e, high(w), i, tm, VNone{}, go.ok(c, e, KNode{b}, high(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, i), and.r(nok(c, a, low(w)), nok(c, b, high(w)), and.r(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelR{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))), and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelR{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))))))
                case ASelN{}:
                  (tm, VEnds{UNil{}}, {==}, hm, alt.n.same(c, a, b, i, none.E(c, a, i, and.l(Bool.not(may(3n, cg2(c), a, rdA(c, i))), Bool.not(may(3n, cg2(c), b, rdA(c, i))), and.l(selq(ASelN{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)), ga, and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelN{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp))), none.E(c, b, i, and.r(Bool.not(may(3n, cg2(c), a, rdA(c, i))), Bool.not(may(3n, cg2(c), b, rdA(c, i))), and.l(selq(ASelN{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)), ga, and.l(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w))), and.r(selq(ASelN{}, may(3n, cg2(c), a, rdA(c, i)), may(3n, cg2(c), b, rdA(c, i))), Bool.and(cell(c, i), Bool.and(nok(c, a, low(w)), nok(c, b, high(w)))), hp)))))
        case KAltR{+b, +Fl}:
          match v:
            case VNone{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+x}:
              pst.bind(c, E(c, b, i), uapp(Fl, E(c, b, i)), o => go(e, SAltM{}, id, i, w, UNil{}, x, o), go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), high(w))), pst.call(c, E(c, b, i), e, high(w), i, tm, VNone{}, go.ok(c, e, KNode{b}, high(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, i), and.l(nok(c, b, high(w)), cell(c, i), and.r(ex(Fl, VEnds{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp)), and.r(nok(c, b, high(w)), cell(c, i), and.r(ex(Fl, VEnds{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp))))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KAltM{Fl, E(c, b, i)}, id, i, w, UNil{}, x, tm2, v2, ga, hR, hm2, and.i(same(x, Fl), ex(E(c, b, i), v2), and.l(ex(Fl, VEnds{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp), hv2)))
            case VOne{+x}:
              pst.bind(c, E(c, b, i), uapp(Fl, E(c, b, i)), o => go(e, SAltM{}, id, i, w, UNil{}, UCon{x, UNil{}}, o), go(e, SNode{}, high(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), high(w))), pst.call(c, E(c, b, i), e, high(w), i, tm, VNone{}, go.ok(c, e, KNode{b}, high(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, high(w)), rdA(c, high(w))}, ga, hR, hm, and.i(nok(c, b, high(w)), cell(c, i), and.l(nok(c, b, high(w)), cell(c, i), and.r(ex(Fl, VOne{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp)), and.r(nok(c, b, high(w)), cell(c, i), and.r(ex(Fl, VOne{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp))))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KAltM{Fl, E(c, b, i)}, id, i, w, UNil{}, UCon{x, UNil{}}, tm2, v2, ga, hR, hm2, and.i(same(UCon{x, UNil{}}, Fl), ex(E(c, b, i), v2), and.l(ex(Fl, VOne{x}), Bool.and(nok(c, b, high(w)), cell(c, i)), hp), hv2)))
            case VNode{+q, +x2}:
              (tm, VStuck{}, {==}, hm, {==})
        case KAltM{+F1, +F2}:
          match v:
            case VNone{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              (tm, vnorm(merge(acc, r)), {==}, hm, ex.vnorm(merge(acc, r), uapp(F1, F2), same.merge2(acc, r, F1, F2, and.l(same(acc, F1), ex(F2, VEnds{r}), hp), and.r(same(acc, F1), ex(F2, VEnds{r}), hp))))
            case VOne{+x}:
              (tm, vnorm(merge(acc, UCon{x, UNil{}})), {==}, hm, ex.vnorm(merge(acc, UCon{x, UNil{}}), uapp(F1, F2), same.merge2(acc, UCon{x, UNil{}}, F1, F2, and.l(same(acc, F1), ex(F2, VOne{x}), hp), and.r(same(acc, F1), ex(F2, VOne{x}), hp))))
            case VNode{+q, +x2}:
              (tm, VStuck{}, {==}, hm, {==})
        case KStarH{+a, +Vs, +i0}:
          match L:
            case UNil{}:
              (tm, vnorm(rev(acc)), {==}, hm, scan.fin(c, a, i0, id, Vs, acc, ga, and.l(Inv(c, a, i0, id, Vs, UNil{}, acc), nok(c, a, w), hp)))
            case UCon{+x, +t}:
              pst.bind(c, E(c, a, x), fil(c, id, E(c, Star{a}, i0)), o => go(e, SStarA{}, id, x, w, t, acc, o), go(e, SNode{}, w, x, 0, UNil{}, UNil{}, call(OO(c, tm, v), w)), pst.call(c, E(c, a, x), e, w, x, tm, v, go.ok(c, e, KNode{a}, w, x, 0, UNil{}, UNil{}, tm, VNode{rdO(c, w), rdA(c, w)}, ga, hR, hm, and.i(nok(c, a, w), cell(c, x), and.r(Inv(c, a, i0, id, Vs, UCon{x, t}, acc), nok(c, a, w), hp), cells.has(c, uapp(Vs, UCon{x, t}), x, inv.p4(c, a, i0, id, Vs, UCon{x, t}, acc, and.l(Inv(c, a, i0, id, Vs, UCon{x, t}, acc), nok(c, a, w), hp)), uapp.in.r(x, Vs, UCon{x, t}, has.self(x, t)))))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KStarA{a, Vs, i0}, id, x, w, t, acc, tm2, v2, ga, hR, hm2, and.i(Inv(c, a, i0, id, Vs, UCon{x, t}, acc), Bool.and(ex(E(c, a, x), v2), nok(c, a, w)), and.l(Inv(c, a, i0, id, Vs, UCon{x, t}, acc), nok(c, a, w), hp), and.i(ex(E(c, a, x), v2), nok(c, a, w), hv2, and.r(Inv(c, a, i0, id, Vs, UCon{x, t}, acc), nok(c, a, w), hp)))))
        case KStarA{+a, +Vs, +i0}:
          match v:
            case VNone{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              %Equal.sym(Out, kp(uO(c), uA(c), unshadow(Entry, tm), id, i), OO(c, tm, VNode{kp.op(kept(c, id, i)), 0}), kp.ok(c, tm, id, i)) : Pst(c, fil(c, id, E(c, Star{a}, i0)), go(e, SStarK{}, id, i, w, merge(L, drop(i, r)), acc, _))
              go.ok(c, e, KStarK{a, Vs, i0}, id, i, w, merge(L, drop(i, r)), acc, tm, VNode{kp.op(kept(c, id, i)), 0}, ga, hR, hm, and.i(Inv(c, a, i0, id, UCon{i, Vs}, merge(L, drop(i, r)), pickc(is.asb(kp.op(kept(c, id, i))), i, acc)), nok(c, a, w), tr.pk(c, a, i0, id, UCon{i, Vs}, merge(L, drop(i, r)), kept(c, id, i), is.asb(kp.op(kept(c, id, i))), i, acc, Equal.sym(Bool, is.asb(kp.op(kept(c, id, i))), kept(c, id, i), is.asb.op(kept(c, id, i))), inv.star(c, a, i0, id, Vs, i, L, r, acc, ga, and.l(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VEnds{r}), nok(c, a, w)), hp), and.l(ex(E(c, a, i), VEnds{r}), nok(c, a, w), and.r(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VEnds{r}), nok(c, a, w)), hp)))), and.r(ex(E(c, a, i), VEnds{r}), nok(c, a, w), and.r(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VEnds{r}), nok(c, a, w)), hp))))
            case VOne{+x}:
              %Equal.sym(Out, kp(uO(c), uA(c), unshadow(Entry, tm), id, i), OO(c, tm, VNode{kp.op(kept(c, id, i)), 0}), kp.ok(c, tm, id, i)) : Pst(c, fil(c, id, E(c, Star{a}, i0)), go(e, SStarK{}, id, i, w, merge(L, drop(i, UCon{x, UNil{}})), acc, _))
              go.ok(c, e, KStarK{a, Vs, i0}, id, i, w, merge(L, drop(i, UCon{x, UNil{}})), acc, tm, VNode{kp.op(kept(c, id, i)), 0}, ga, hR, hm, and.i(Inv(c, a, i0, id, UCon{i, Vs}, merge(L, drop(i, UCon{x, UNil{}})), pickc(is.asb(kp.op(kept(c, id, i))), i, acc)), nok(c, a, w), tr.pk(c, a, i0, id, UCon{i, Vs}, merge(L, drop(i, UCon{x, UNil{}})), kept(c, id, i), is.asb(kp.op(kept(c, id, i))), i, acc, Equal.sym(Bool, is.asb(kp.op(kept(c, id, i))), kept(c, id, i), is.asb.op(kept(c, id, i))), inv.star(c, a, i0, id, Vs, i, L, UCon{x, UNil{}}, acc, ga, and.l(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VOne{x}), nok(c, a, w)), hp), and.l(ex(E(c, a, i), VOne{x}), nok(c, a, w), and.r(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VOne{x}), nok(c, a, w)), hp)))), and.r(ex(E(c, a, i), VOne{x}), nok(c, a, w), and.r(Inv(c, a, i0, id, Vs, UCon{i, L}, acc), Bool.and(ex(E(c, a, i), VOne{x}), nok(c, a, w)), hp))))
            case VNode{+q, +x2}:
              (tm, VStuck{}, {==}, hm, {==})
        case KStarK{+a, +Vs, +i0}:
          match v:
            case VNone{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              (tm, VStuck{}, {==}, hm, {==})
            case VOne{+x}:
              (tm, VStuck{}, {==}, hm, {==})
            case VNode{+q, +x2}:
              match q:
                case OLit{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OCls{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OAlt{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OCat{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OCatS{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OCatSC{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OStar{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OStarC{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case ORefM{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case ORef{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OEmp{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case OBad{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case ASelB{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, UCon{i, acc}, tm, VNone{}, ga, hR, hm, hp)
                case ASelL{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case ASelR{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
                case ASelN{}:
                  go.ok(c, e, KStarH{a, UCon{i, Vs}, i0}, id, i, w, L, acc, tm, VNone{}, ga, hR, hm, hp)
        case KRefM{}:
          match v:
            case VNone{}:
              pst.bind(c, E(c, rl(c, w), i), E(c, rl(c, w), i), o => go(e, SStore{}, id, i, w, UNil{}, UNil{}, o), go(e, SNode{}, low(w), i, 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), low(w))), pst.call(c, E(c, rl(c, w), i), e, low(w), i, tm, VNone{}, go.ok(c, e, KNode{rl(c, w)}, low(w), i, 0, UNil{}, UNil{}, tm, VNode{rdO(c, low(w)), rdA(c, low(w))}, ga, hR, hm, and.i(nok(c, rl(c, w), low(w)), cell(c, i), and.l(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VNone{}), and.r(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VNone{})), hp)), and.l(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VNone{})), hp)))), +tm2 => +v2 => +hm2 => +hv2 => go.ok(c, e, KStore{}, id, i, w, UNil{}, UNil{}, tm2, v2, ga, hR, hm2, and.i(cell(c, i), ex(E(c, rl(c, w), i), v2), and.l(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VNone{})), hp), hv2)))
            case VStuck{}:
              (tm, VStuck{}, {==}, hm, {==})
            case VEnds{+r}:
              (tm, VEnds{r}, {==}, hm, and.r(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VEnds{r}), and.r(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VEnds{r})), hp)))
            case VOne{+r}:
              (tm, VOne{r}, {==}, hm, and.r(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VOne{r}), and.r(cell(c, i), Bool.and(nok(c, rl(c, w), low(w)), mst(E(c, rl(c, w), i), VOne{r})), hp)))
            case VNode{+q, +x2}:
              (tm, VStuck{}, {==}, hm, {==})
        case KStore{}:
          store.ok(c, tm, v, i, w, hm, and.l(cell(c, i), ex(E(c, rl(c, w), i), v), hp), and.r(cell(c, i), ex(E(c, rl(c, w), i), v), hp))
# ---- the end of the input ----

law textp.step:
  for +c: Cx
  for +a: Char
  for +t: String
  for +i: U32
  for +end: U32
  for +ok: Bool
  for +h: T(Bool.and(Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295)))), Bool.and(at(c, t, (i + 1 : U32)), U32.is_eq(pos((i + 1 : U32), t), end))))
  T(Bool.and(ok, Bool.and(at(c, SCon{a, t}, i), U32.is_eq(pos(i, SCon{a, t}), end))))

def textp.step(c, a, t, i, end, ok, h):
  +h1 = and.l(Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295)))), Bool.and(at(c, t, (i + 1 : U32)), U32.is_eq(pos((i + 1 : U32), t), end)), h)
  +h2 = and.r(Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295)))), Bool.and(at(c, t, (i + 1 : U32)), U32.is_eq(pos((i + 1 : U32), t), end)), h)
  and.i(ok, Bool.and(at(c, SCon{a, t}, i), U32.is_eq(pos(i, SCon{a, t}), end)), and.l(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295))), h1), and.i(at(c, SCon{a, t}, i), U32.is_eq(pos(i, SCon{a, t}), end), and.i(Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295))), at(c, t, (i + 1 : U32)), and.r(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295))), h1), and.l(at(c, t, (i + 1 : U32)), U32.is_eq(pos((i + 1 : U32), t), end), h2)), and.r(at(c, t, (i + 1 : U32)), U32.is_eq(pos((i + 1 : U32), t), end), h2)))

law textp.at:
  for s: String
  for +c: Cx
  for +i: U32
  for +end: U32
  for +ok: Bool
  for +h: T(textp(c, s, i, end, ok))
  T(Bool.and(ok, Bool.and(at(c, s, i), U32.is_eq(pos(i, s), end))))

def textp.at(s, c, i, end, ok, h):
  match s:
    case SNil{}:
      h
    case SCon{+a, +t}:
      textp.step(c, a, t, i, end, ok, textp.at(t, c, (i + 1 : U32), end, Bool.and(ok, Bool.and(U32.is_eq(rdA(c, i), Char.to_u32(a)), Bool.not(U32.is_eq(Char.to_u32(a), 4294967295)))), h))

def okm(m: Maybe<&2, Bool>, +S0: Bool) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      bi(b, S0)

law final.up:
  for +c: Cx
  for +r2: R
  for +e: U32
  for +S0: String
  for +hS: {suf(c, cnx(c)) == S0 : String}
  for +eS: {S0 == cS(c) : String}
  for +ga: T(Glob(c))
  for +hpos: T(U32.is_eq(pos(cnx(c), S0), e))
  for +ht: T(TR(c, r2, S0))
  T(has(e, E(c, r2, cnx(c))))

law tr.Ex2:
  for +c: Cx
  for +r2: R
  for +x: String
  for +y: String
  for +z: U32
  for +w0: U32
  for +w: U32
  for +e1: {x == y : String}
  for +e2: T(U32.is_eq(w0, w))
  for +h: T(has(w0, E.go(c, r2, "", x, z)))
  T(has(w, E.go(c, r2, "", y, z)))

def tr.Ex2(c, r2, x, y, z, w0, w, e1, e2, h):
  tr.Eq2(c, r2, x, z, w0, w, y, e1, u32.eq.t(w0, w, e2), h)

def final.up(c, r2, e, S0, hS, eS, ga, hpos, ht):
  tr.Ex2(c, r2, S0 ++ "", suf(c, cnx(c)), cnx(c), pos(cnx(c), S0), e, Equal.trans(String, S0 ++ "", S0, suf(c, cnx(c)), app.nil(S0), Equal.sym(String, suf(c, cnx(c)), S0, hS)), hpos, E.intro(c, r2, S0, "", "", cnx(c), ht))

law final.down.k:
  for +c: Cx
  for +r2: R
  for +e: U32
  for +S0: String
  for +hS: {suf(c, cnx(c)) == S0 : String}
  for +eS: {S0 == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for w: EW(c, r2, "", suf(c, cnx(c)), cnx(c), e)
  T(TR(c, r2, S0))

law at.of.app:
  for +c: Cx
  for +q: String
  for +y: String
  for +S0: String
  for +e: U32
  for +ga: T(Glob(c))
  for +eS: {q ++ y == cS(c) : String}
  for +e2: {pos(cnx(c), q) == e : U32}
  T(at(c, y, e))

def at.of.app(c, q, y, S0, e, ga, eS, e2):
  %e2 : T(at(c, y, _))
  at.pos(c, q, y, cnx(c), cell.rec.at(c, q, y, ga, eS))

law tr.TR.y:
  for +c: Cx
  for +r2: R
  for +q: String
  for +y: String
  for +S0: String
  for +ey: {y == "" : String}
  for +e1: {q ++ y == S0 : String}
  for +ht: T(TR(c, r2, q))
  T(TR(c, r2, S0))

def tr.TR.y(c, r2, q, y, S0, ey, e1, ht):
  %e1 : T(TR(c, r2, _))
  %Equal.sym(String, y, "", ey) : T(TR(c, r2, q ++ _))
  tr.tr(c, r2, q, q ++ "", app.nil.sym(q), ht)

def final.down.k(c, r2, e, S0, hS, eS, ga, hend, w):
  match w:
    case (+q, +y, +e1, e2, ht):
      +e3 = e2
      +e4 = Equal.trans(String, q ++ y, suf(c, cnx(c)), S0, e1, hS)
      tr.TR.y(c, r2, q, y, S0, at.inj(c, y, "", e, at.of.app(c, q, y, S0, e, ga, Equal.trans(String, q ++ y, S0, cS(c), e4, eS), e3), hend), e4, ht)

law final.bi:
  for +c: Cx
  for +r2: R
  for +e: U32
  for +S0: String
  for +hS: {suf(c, cnx(c)) == S0 : String}
  for +eS: {S0 == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), S0), e))
  T(bi(has(e, E(c, r2, cnx(c))), TR(c, r2, S0)))

def final.bi(c, r2, e, S0, hS, eS, ga, hend, hpos):
  bi.i(has(e, E(c, r2, cnx(c))), TR(c, r2, S0), +h => final.down.k(c, r2, e, S0, hS, eS, ga, hend, E.elim(c, r2, suf(c, cnx(c)), "", cnx(c), e, h)), +ht => final.up(c, r2, e, S0, hS, eS, ga, hpos, ht))

law fin.bi:
  for +c: Cx
  for +r: R
  for +e: U32
  for +l: UL
  for +hS: {suf(c, cnx(c)) == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), cS(c)), e))
  for +hs: T(same(l, E(c, inl(12n, cg(c), r), cnx(c))))
  T(bi(has(e, l), TR(c, r, cS(c))))

def fin.bi(c, r, e, l, hS, ga, hend, hpos, hs):
  +E0 = E(c, inl(12n, cg(c), r), cnx(c))
  bi.trans(has(e, l), has(e, E(c, inl(12n, cg(c), r), cnx(c))), TR(c, r, cS(c)), bi.i(has(e, l), has(e, E(c, inl(12n, cg(c), r), cnx(c))), +h => sub.has(e, l, E(c, inl(12n, cg(c), r), cnx(c)), same.l(l, E(c, inl(12n, cg(c), r), cnx(c)), hs), h), +h => sub.has(e, E(c, inl(12n, cg(c), r), cnx(c)), l, same.r(l, E(c, inl(12n, cg(c), r), cnx(c)), hs), h)), bi.trans(has(e, E(c, inl(12n, cg(c), r), cnx(c))), TR(c, inl(12n, cg(c), r), cS(c)), TR(c, r, cS(c)), final.bi(c, inl(12n, cg(c), r), e, cS(c), hS, {==}, ga, hend, hpos), inl.eq(c, 12n, r, cS(c), "", "", app.nil(cS(c)))))
# ---- putting it together ----

law fast.fin.v:
  for +c: Cx
  for +r: R
  for +e: U32
  for +tm2: Tree<Entry>
  for v2: V
  for +hS: {suf(c, cnx(c)) == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), cS(c)), e))
  for +hx: T(ex(E(c, inl(12n, cg(c), r), cnx(c)), v2))
  T(okm(fast.fin(OO(c, tm2, v2), e), TR(c, r, cS(c))))

law fin.one:
  for +c: Cx
  for +r: R
  for +e: U32
  for +x: U32
  for +hS: {suf(c, cnx(c)) == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), cS(c)), e))
  for +hx: T(same(UCon{x, UNil{}}, E(c, inl(12n, cg(c), r), cnx(c))))
  T(bi(U32.is_eq(x, e), TR(c, r, cS(c))))

def fin.one(c, r, e, x, hS, ga, hend, hpos, hx):
  %or.false.r(U32.is_eq(x, e)) : T(bi(_, TR(c, r, cS(c))))
  fin.bi(c, r, e, UCon{x, UNil{}}, hS, ga, hend, hpos, hx)

def fast.fin.v(c, r, e, tm2, v2, hS, ga, hend, hpos, hx):
  match v2:
    case VNone{}:
      {==}
    case VStuck{}:
      {==}
    case VEnds{+l}:
      fin.bi(c, r, e, l, hS, ga, hend, hpos, hx)
    case VOne{+x}:
      fin.one(c, r, e, x, hS, ga, hend, hpos, hx)
    case VNode{q, w}:
      {==}

law fin.do:
  for +c: Cx
  for +r: R
  for +e: U32
  for -o: Out
  for h: Pst(c, E(c, inl(12n, cg(c), r), cnx(c)), o)
  for +hS: {suf(c, cnx(c)) == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), cS(c)), e))
  T(okm(fast.fin(o, e), TR(c, r, cS(c))))

def fin.do(c, r, e, o, h, hS, ga, hend, hpos):
  match h:
    case (+tm2, +v2, e0, hm2, hx):
      %Equal.sym(Out, o, OO(c, tm2, v2), e0) : T(okm(fast.fin(_, e), TR(c, r, cS(c))))
      fast.fin.v(c, r, e, tm2, v2, hS, ga, hend, hpos, hx)

law fast.run.k:
  for +c: Cx
  for +r: R
  for +rt: U32
  for +f: Nat
  for +e: U32
  for +d: Nat
  for +hS: {suf(c, cnx(c)) == cS(c) : String}
  for +ga: T(Glob(c))
  for +hend: T(at(c, "", e))
  for +hpos: T(U32.is_eq(pos(cnx(c), cS(c)), e))
  for +hR: T(rulesp(c, crt(c)))
  for +hnok: T(nok(c, inl(12n, cg(c), r), rt))
  for +hcell: T(cell(c, cnx(c)))
  for w: NewW(c, Array.new(Entry, d, ENone{}))
  T(okm(fast.fin(go(f, SNode{}, rt, cnx(c), 0, UNil{}, UNil{}, call(O{uO(c), uA(c), Array.new(Entry, d, ENone{}), VNone{}}, rt)), e), TR(c, r, cS(c))))

def fast.run.k(c, r, rt, f, e, d, hS, ga, hend, hpos, hR, hnok, hcell, w):
  match w:
    case (+tm, e0, hm):
      %Equal.sym(Array<Entry>, Array.new(Entry, d, ENone{}), unshadow(Entry, tm), e0) : T(okm(fast.fin(go(f, SNode{}, rt, cnx(c), 0, UNil{}, UNil{}, call(O{uO(c), uA(c), _, VNone{}}, rt)), e), TR(c, r, cS(c))))
      fin.do(c, r, e, go(f, SNode{}, rt, cnx(c), 0, UNil{}, UNil{}, call(OO(c, tm, VNone{}), rt)), pst.call(c, E(c, inl(12n, cg(c), r), cnx(c)), f, rt, cnx(c), tm, VNone{}, go.ok(c, f, KNode{inl(12n, cg(c), r)}, rt, cnx(c), 0, UNil{}, UNil{}, tm, VNode{rdO(c, rt), rdA(c, rt)}, ga, hR, hm, and.i(nok(c, inl(12n, cg(c), r), rt), cell(c, cnx(c)), hnok, hcell))), hS, ga, hend, hpos)

law fast.run.ok:
  for +c: Cx
  for +r: R
  for +rt: U32
  for +f: Nat
  for +e: U32
  for +hv: T(vals(c, inl(12n, cg(c), r), rt, cS(c), cnx(c), e))
  T(okm(fast.run(uB(c), rt, f, e, cnx(c)), TR(c, r, cS(c))))

def fast.run.ok(c, r, rt, f, e, hv):
  +hR = and.l(rulesp(c, crt(c)), Bool.and(nok(c, inl(12n, cg(c), r), rt), textp(c, cS(c), cnx(c), e, True{})), hv)
  +hr = and.r(rulesp(c, crt(c)), Bool.and(nok(c, inl(12n, cg(c), r), rt), textp(c, cS(c), cnx(c), e, True{})), hv)
  +hn = and.l(nok(c, inl(12n, cg(c), r), rt), textp(c, cS(c), cnx(c), e, True{}), hr)
  +ht = textp.at(cS(c), c, cnx(c), e, True{}, and.r(nok(c, inl(12n, cg(c), r), rt), textp(c, cS(c), cnx(c), e, True{}), hr))
  +ga = and.l(at(c, cS(c), cnx(c)), U32.is_eq(pos(cnx(c), cS(c)), e), ht)
  +hpos = and.r(at(c, cS(c), cnx(c)), U32.is_eq(pos(cnx(c), cS(c)), e), ht)
  +hend = at.of.app(c, cS(c), "", cS(c), e, ga, app.nil(cS(c)), u32.eq.t(pos(cnx(c), cS(c)), e, hpos))
  fast.run.k(c, r, rt, f, e, Nat.min(20n, 1n+bits(32n, e)), suf.self(cS(c), cnx(c)), ga, hend, hpos, hR, hn, cell.self(cS(c), cnx(c)), new.w(c, Nat.min(20n, 1n+bits(32n, e))))

law fast.fin3.b:
  for v: Bool
  for +c: Cx
  for +r: R
  for +rt: U32
  for +f: Nat
  for +e: U32
  for +hv: {v == vals(c, inl(12n, cg(c), r), rt, cS(c), cnx(c), e) : Bool}
  T(okm(fast.fin3((uB(c), v), rt, f, e, cnx(c)), TR(c, r, cS(c))))

def fast.fin3.b(v, c, r, rt, f, e, hv):
  match v:
    case False{}:
      {==}
    case True{}:
      fast.run.ok(c, r, rt, f, e, Equal.sym(Bool, True{}, vals(c, inl(12n, cg(c), r), rt, cS(c), cnx(c), e), hv))

law fast.w2:
  for +tO: Tree<Op>
  for +tA: Tree<U32>
  for +g0: Gram
  for +t: RT
  for +r: R
  for +s: String
  for +rt: U32
  for +f: Nat
  for +st0: U32
  for +e: U32
  T(okm(fast.fin3(validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, B{unshadow(Op, tO), unshadow(U32, tA)}), rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.w2(tO, tA, g0, t, r, s, rt, f, st0, e):
  %Equal.sym(B & Bool, validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, B{unshadow(Op, tO), unshadow(U32, tA)}), (uB(Cx{g0, s, st0, t, tO, tA}), vals(Cx{g0, s, st0, t, tO, tA}, inl(12n, g0, r), rt, s, st0, e)), val.ok(Cx{g0, s, st0, t, tO, tA}, inl(12n, g0, r), rt, s, st0, e)) : T(okm(fast.fin3(_, rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))
  fast.fin3.b(vals(Cx{g0, s, st0, t, tO, tA}, inl(12n, g0, r), rt, s, st0, e), Cx{g0, s, st0, t, tO, tA}, r, rt, f, e, {==})

law fast.bz.k:
  for -ops: Array<Op>
  for -a: Array<U32>
  for +g0: Gram
  for +t: RT
  for +r: R
  for +s: String
  for +rt: U32
  for +f: Nat
  for +st0: U32
  for +e: U32
  for w1: &t: Tree<Op> -> {unshadow(Op, t) == ops : Array<Op>}
  for w2: &t: Tree<U32> -> {unshadow(U32, t) == a : Array<U32>}
  T(okm(fast.fin3(validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, B{ops, a}), rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.bz.k(ops, a, g0, t, r, s, rt, f, st0, e, w1, w2):
  match w1:
    case (+tO, e1):
      match w2:
        case (+tA, e2):
          %e1 : T(okm(fast.fin3(validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, B{_, a}), rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))
          %e2 : T(okm(fast.fin3(validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, B{unshadow(Op, tO), _}), rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))
          fast.w2(tO, tA, g0, t, r, s, rt, f, st0, e)

law fast.bz:
  for b: B
  for +g0: Gram
  for +t: RT
  for +r: R
  for +s: String
  for +rt: U32
  for +f: Nat
  for +st0: U32
  for +e: U32
  T(okm(fast.fin3(validate(inlg(12n, g0, g0), t, inl(12n, g0, r), rt, s, st0, e, b), rt, f, e, st0), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.bz(b, g0, t, r, s, rt, f, st0, e):
  match b:
    case B{ops, a}:
      fast.bz.k(ops, a, g0, t, r, s, rt, f, st0, e, shape(Op, ops), shape(U32, a))

law fast.fin2.ok:
  for p: B & U32
  for +g0: Gram
  for +t: RT
  for +r: R
  for +s: String
  for +rt: U32
  for +f: Nat
  for +st0: U32
  T(okm(fast.fin2(p, inlg(12n, g0, g0), t, inl(12n, g0, r), s, rt, f, st0), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.fin2.ok(p, g0, t, r, s, rt, f, st0):
  match p:
    case (b, +e):
      fast.bz(b, g0, t, r, s, rt, f, st0, e)

law fast.text.ok:
  for b: B
  for +g0: Gram
  for +t: RT
  for +r: R
  for +nx: U32
  for +rt: U32
  for +s: String
  T(okm(fast.text(b, inlg(12n, g0, g0), t, inl(12n, g0, r), nx, rt, s), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.text.ok(b, g0, t, r, nx, rt, s):
  fast.fin2.ok(write(s, nx, b), g0, t, r, s, rt, Nat.add(Nat.mul(64n, String.length(s)), 4096n), nx)

law fast.k.ok:
  for p: B & U32
  for +t: RT
  for +g0: Gram
  for +r: R
  for +s: String
  T(okm(fast.k(p, t, inlg(12n, g0, g0), inl(12n, g0, r), s), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.k.ok(p, t, g0, r, s):
  match p:
    case (b, +nx):
      fast.text.ok(emit(t, inlg(12n, g0, g0), inl(12n, g0, r), nx, b), g0, t, r, (nx + rsize(inl(12n, g0, r)) : U32), root(inl(12n, g0, r), nx), s)

law fast.go.ok:
  for +g0: Gram
  for +r: R
  for +s: String
  for +code: U32
  for +n: U32
  T(okm(fast.go(inlg(12n, g0, g0), inl(12n, g0, r), s, code, n), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.go.ok(g0, r, s, code, n):
  fast.k.ok(emit_all(roots(inlg(12n, g0, g0), inlg(12n, g0, g0), 16), inlg(12n, g0, g0), inlg(12n, g0, g0), 16, B{[OEmp{} : Op^bits(32n, code)], [0 : U32^bits(32n, (code + n : U32))]}), roots(inlg(12n, g0, g0), inlg(12n, g0, g0), 16), g0, r, s)

law fast.size.ok:
  for ok: Bool
  for +g0: Gram
  for +r: R
  for +s: String
  for +code: U32
  T(okm(fast.size(ok, inlg(12n, g0, g0), inl(12n, g0, r), s, code), sem(1n+bound(g0, s), g0, r, s, "")))

def fast.size.ok(ok, g0, r, s, code):
  match ok:
    case True{}:
      fast.go.ok(g0, r, s, code, (U32.from_nat(String.length(s)) + 4 : U32))
    case False{}:
      {==}

law pick.eq:
  for m: Maybe<&2, Bool>
  for +S0: Bool
  for +h: T(okm(m, S0))
  {full.pick(m, u => S0) == S0 : Bool}

def pick.eq(m, S0, h):
  match m:
    case None{}:
      {==}
    case Some{b}:
      bi.eq(b, S0, h)

law full.eq:
  for +g: Gram
  for +r: R
  for +s: String
  {full.go(g, r, s) == sem(1n+bound(g, s), g, r, s, "") : Bool}

def full.eq(g, r, s):
  pick.eq(fast(g, r, s), sem(1n+bound(g, s), g, r, s, ""), fast.size.ok(U32.is_lt(((gsize(inlg(12n, g, g), inlg(12n, g, g)) + rsize(inl(12n, g, r)) : U32) + 32 : U32), 60000), g, r, s, ((gsize(inlg(12n, g, g), inlg(12n, g, g)) + rsize(inl(12n, g, r)) : U32) + 32 : U32)))

law fast.ok:
  for +g: Gram
  for +r: R
  for +s: String
  {full.run(g, r, s) == sem(1n+bound(g, s), g, r, s, "") : Bool}

def fast.ok(g, r, s):
  match s:
    case SNil{}:
      full.eq(g, r, SNil{})
    case SCon{+h, +t}:
      full.eq(g, r, SCon{h, t})

# ---- from the matcher to the laws ----

def to_gram(g: List<(String & R)>) -> Gram:
  match g:
    case Nil{}:
      GNil{}
    case Con{(k, r), t}:
      GCon{k, r, to_gram(t)}

def from_gram(g: Gram) -> List<(String & R)>:
  match g:
    case GNil{}:
      Nil{}
    case GCon{k, r, t}:
      (k, r) <> from_gram(t)

def fuel(b: Bk, s: String) -> Nat:
  match b:
    case Limit{d, g}:
      d
    case Full{g}:
      bound(g, s)

def gram(b: Bk) -> Gram:
  match b:
    case Limit{d, g}:
      g
    case Full{g}:
      g

def check.run(+b: Bk, +r: R, +x: String) -> Bool:
  match b:
    case Limit{d, g}:
      sem(1n+d, g, r, x, "")
    case Full{g}:
      full.run(g, r, x)

def ck(+b: Bk, r: R, +x: String) -> Bool:
  sem(1n+fuel(b, x), gram(b), r, x, "")

law run.ok:
  for +b: Bk
  for +r: R
  for +s: String
  {check.run(b, r, s) == ck(b, r, s) : Bool}

def run.ok(b, r, s):
  match b:
    case Limit{d, g}:
      {==}
    case Full{g}:
      fast.ok(g, r, s)

law run.sym:
  for +b: Bk
  for +r: R
  for +s: String
  {ck(b, r, s) == check.run(b, r, s) : Bool}

def run.sym(b, r, s):
  Equal.sym(Bool, check.run(b, r, s), ck(b, r, s), run.ok(b, r, s))

law to.ck:
  for +b: Bk
  for +r: R
  for +s: String
  for +h: T(check.run(b, r, s))
  T(ck(b, r, s))

def to.ck(b, r, s, h):
  %run.ok(b, r, s) : {_ == True{} : Bool}
  h

law from.ck:
  for +b: Bk
  for +r: R
  for +s: String
  for +h: T(ck(b, r, s))
  T(check.run(b, r, s))

def from.ck(b, r, s, h):
  %run.sym(b, r, s) : {_ == True{} : Bool}
  h

law any.k:
  for +b: Bk
  for +x: String
  for +r: R
  for w: ExW(1n+fuel(b, x), gram(b), r, x)
  exs m: Nat
  T(check.run(b, exact(m, r), x))

def any.k(b, x, r, w):
  match w:
    case (+m, hm):
      (m, from.ck(b, exact(m, r), x, hm))

law atl.fix:
  for +b: Bk
  for +x: String
  for +r: R
  for -n: Nat
  for w: AtlW(1n+fuel(b, x), gram(b), r, x, n)
  exs m: Nat
  T(Nat.is_le(n, m)) & T(check.run(b, exact(m, r), x))

def atl.fix(b, x, r, n, w):
  match w:
    case (+m, hle, hm):
      (m, hle, from.ck(b, exact(m, r), x, hm))

law rpt.fix:
  for +b: Bk
  for +x: String
  for +r: R
  for -a: Nat
  for -c: Nat
  for w: RptW(1n+fuel(b, x), gram(b), r, x, a, c)
  exs m: Nat
  T(Nat.is_le(a, m)) & T(Nat.is_le(m, c)) & T(check.run(b, exact(m, r), x))

def rpt.fix(b, x, r, a, c, w):
  match w:
    case (+m, ha, hc, hm):
      (m, ha, hc, from.ck(b, exact(m, r), x, hm))

law atm.fix:
  for +b: Bk
  for +x: String
  for +r: R
  for -n: Nat
  for w: RptW(1n+fuel(b, x), gram(b), r, x, 0n, n)
  exs m: Nat
  T(Nat.is_le(m, n)) & T(check.run(b, exact(m, r), x))

def atm.fix(b, x, r, n, w):
  match w:
    case (+m, ha, hb, hm):
      (m, hb, from.ck(b, exact(m, r), x, hm))

law lift:
  for +b: Bk
  for +y: String
  for +S: String
  for +u: String
  for +v: String
  for +h: {u ++ (y ++ v) == S : String}
  for +r: R
  for +hm: T(sem(1n+fuel(b, y), gram(b), r, y, ""))
  T(sem(1n+fuel(b, S), gram(b), r, y, ""))

def lift(b, y, S, u, v, h, r, hm):
  match b:
    case Limit{d, g}:
      hm
    case Full{+g}:
      complete(1n+bound(g, y), g, S, r, y, u, v, h, hm)

law lower:
  for +b: Bk
  for +s: String
  for +y: String
  for +r: R
  for +hm: T(sem(1n+fuel(b, s), gram(b), r, y, ""))
  T(sem(1n+fuel(b, y), gram(b), r, y, ""))

def lower(b, s, y, r, hm):
  match b:
    case Limit{d, g}:
      hm
    case Full{+g}:
      complete(1n+bound(g, s), g, y, r, y, "", "", app.nil(y), hm)

law app.nil.right:
  for -x: String
  for y: String
  {x ++ (y ++ "") == x ++ y : String}

def app.nil.right(x, y):
  %app.nil(y) : {x ++ (y ++ "") == x ++ _ : String}
  {==}

# ---- the laws ----

def L.Rule():
  R

def L.Book():
  Bk

def L.check.era(book, r, s):
  +b = book
  +r2 = r
  +x = s
  check.run(b, r2, x)

def L.check(book, r, s):
  +b = book
  +r2 = r
  +x = s
  (b, r2, x, L.check.era(b, r2, x))

def L.check.borrows(book, r, s, book2, r2, s2, val, h):
  %h : {Pair.fst(L.Book, L.Rule & String & Bool, _) == book : L.Book} & {Pair.fst(L.Rule, String & Bool, Pair.snd(L.Book, L.Rule & String & Bool, _)) == r : L.Rule} & {Pair.fst(String, Bool, Pair.snd(L.Rule, String & Bool, Pair.snd(L.Book, L.Rule & String & Bool, _))) == s : String}
  ({==}, {==}, {==})

def L.check.era.ok(book, r, s, book2, r2, s2, val, h):
  %h : {Pair.snd(String, Bool, Pair.snd(L.Rule, String & Bool, Pair.snd(L.Book, L.Rule & String & Bool, _))) == L.check.era(book, r, s) : Bool}
  {==}

def L.limit(d, g):
  Limit{d, to_gram(g)}

def L.full(g):
  Full{to_gram(g)}

def L.full.intro(d, g, r, s, h):
  +x = s
  +r2 = r
  +G = to_gram(g)
  from.ck(Full{G}, r2, x, complete(1n+d, G, x, r2, x, "", "", app.nil(x), h))

def L.full.elim(g, r, s, h):
  +G = to_gram(g)
  +x = s
  +r2 = r
  (bound(G, x), to.ck(Full{G}, r2, x, h))

def L.lookup.era(g, name):
  lk(to_gram(g), name)

law C.lookup.nil:
  for book: L.Book
  for name: String
  for s: String
  {ck(book, L.lookup.era([], name), s) == False{} : Bool}

def C.lookup.nil(book, name, s):
  {==}

law pf.lookup.nil:
  for book: L.Book
  for name: String
  for s: String
  {L.check.era(book, L.lookup.era([], name), s) == False{} : Bool}

def pf.lookup.nil(book, name, s):
  +book__ = book
  +name__ = name
  +s__ = s
  %run.sym(book__, L.lookup.era([], name__), s__) : {_ == False{} : Bool}
  C.lookup.nil(book__, name__, s__)

law lk.pick.sem:
  for e: Bool
  for +d: Nat
  for +g: Gram
  for +r: R
  for +rest: R
  for +x: String
  {sem(1n+d, g, lk.pick(e, r, rest), x, "") == (e && sem(1n+d, g, r, x, "")) || sem(1n+d, g, rest, x, "") : Bool}

def lk.pick.sem(e, d, g, r, rest, x):
  match e:
    case False{}:
      {==}
    case True{}:
      or.eq(sem(1n+d, g, r, x, ""), sem(1n+d, g, rest, x, ""))

law pf.lookup.con:
  for book: L.Book
  for k: String
  for r: L.Rule
  for g: List<(String & L.Rule)>
  for name: String
  for s: String
  {L.check.era(book, L.lookup.era((k, r) <> g, name), s) == (String.eq(String.to_lower(k), String.to_lower(name)) && L.check.era(book, r, s)) || L.check.era(book, L.lookup.era(g, name), s) : Bool}

def pf.lookup.con(book, k, r, g, name, s):
  +b = book
  +x = s
  +r2 = r
  +n = name
  +k2 = k
  +G = to_gram(g)
  %run.sym(b, lk.pick(String.eq(String.to_lower(k2), String.to_lower(n)), r2, lk(G, n)), x) : {_ == (String.eq(String.to_lower(k), String.to_lower(name)) && L.check.era(book, r, s)) || L.check.era(book, L.lookup.era(g, name), s) : Bool}
  %run.sym(b, r2, x) : {ck(b, lk.pick(String.eq(String.to_lower(k2), String.to_lower(n)), r2, lk(G, n)), x) == (String.eq(String.to_lower(k), String.to_lower(name)) && _) || L.check.era(book, L.lookup.era(g, name), s) : Bool}
  %run.sym(b, lk(G, n), x) : {ck(b, lk.pick(String.eq(String.to_lower(k2), String.to_lower(n)), r2, lk(G, n)), x) == (String.eq(String.to_lower(k), String.to_lower(name)) && ck(b, r2, x)) || _ : Bool}
  lk.pick.sem(String.eq(String.to_lower(k2), String.to_lower(n)), fuel(b, x), gram(b), r2, lk(G, n), x)

def L.lookup(g, name):
  +G = to_gram(g)
  +n = name
  (from_gram(G), n, lk(G, n))

def L.lookup.era.ok(g, name, g2, name2, r, h):
  %h : {Pair.snd(String, L.Rule, Pair.snd(List<(String & L.Rule)>, String & L.Rule, _)) == L.lookup.era(g, name) : L.Rule}
  {==}

# An or, written the way List.any unfolds it.
law any.or:
  for a: Bool
  for -b: Bool
  {a || b == List.any.if(u => b, a) : Bool}

def any.or(a, b):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# The rule lookup.era finds matches what some definition of the name matches.
law lk.any:
  for +book: L.Book
  for +name: String
  for +s: String
  for G: Gram
  {L.check.era(book, L.lookup.era(from_gram(G), name), s) == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), from_gram(G)) : Bool}

def lk.any(book, name, s, G):
  match G:
    case GNil{}:
      pf.lookup.nil(book, name, s)
    case GCon{+k, +r, +T}:
      %Equal.sym(Bool, L.check.era(book, L.lookup.era((k, r) <> from_gram(T), name), s), (String.eq(String.to_lower(k), String.to_lower(name)) && L.check.era(book, r, s)) || L.check.era(book, L.lookup.era(from_gram(T), name), s), pf.lookup.con(book, k, r, from_gram(T), name, s)) : {_ == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), (k, r) <> from_gram(T)) : Bool}
      %Equal.sym(Bool, L.check.era(book, L.lookup.era(from_gram(T), name), s), List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), from_gram(T)), lk.any(book, name, s, T)) : {(String.eq(String.to_lower(k), String.to_lower(name)) && L.check.era(book, r, s)) || _ == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), (k, r) <> from_gram(T)) : Bool}
      any.or(String.eq(String.to_lower(k), String.to_lower(name)) && L.check.era(book, r, s), List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), from_gram(T)))

law fg.eq:
  for -g: List<(String & L.Rule)>
  for -G: Gram
  for e1: {to_gram(g) == G : Gram}
  for e2: {from_gram(to_gram(g)) == g : List<(String & L.Rule)>}
  {from_gram(G) == g : List<(String & L.Rule)>}

def fg.eq(g, G, e1, e2):
  %e1 : {from_gram(_) == g : List<(String & L.Rule)>}
  e2

law lk.any.at:
  for -g: List<(String & L.Rule)>
  for +G: Gram
  for +name: String
  for +book: L.Book
  for +s: String
  for q: {from_gram(G) == g : List<(String & L.Rule)>}
  {L.check.era(book, L.lookup.era(g, name), s) == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), g) : Bool}

def lk.any.at(g, G, name, book, s, q):
  %q : {L.check.era(book, L.lookup.era(_, name), s) == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), _) : Bool}
  lk.any(book, name, s, G)

def L.ref(name):
  Ref{name}

def L.ref.zero(g, name, s):
  {==}

def L.ref.succ(g, name, s, d):
  {==}

def L.matches.era(g, name, s):
  L.check.era(L.full(g), L.ref(name), s)

def L.matches(g, name, s):
  +G = to_gram(g)
  +n = name
  +x = s
  (from_gram(G), n, x, L.check.era(Full{G}, Ref{n}, x))

def ConvW(g: List<(String & R)>) -> Type:
  &G: Gram -> {to_gram(g) == G : Gram} & {from_gram(to_gram(g)) == g : List<(String & R)>}

law conv.k:
  for +k: String
  for +r: R
  for -t: List<(String & R)>
  for w: ConvW(t)
  ConvW((k, r) <> t)

law conv.k.eq1:
  for -k: String
  for -r: R
  for -t: Gram
  for -G: Gram
  for e: {t == G : Gram}
  {GCon{k, r, t} == GCon{k, r, G} : Gram}

def conv.k.eq1(k, r, t, G, e):
  %e : {GCon{k, r, t} == GCon{k, r, _} : Gram}
  {==}

law conv.k.eq2:
  for -k: String
  for -r: R
  for -l: List<(String & R)>
  for -t: List<(String & R)>
  for e: {l == t : List<(String & R)>}
  {(k, r) <> l == (k, r) <> t : List<(String & R)>}

def conv.k.eq2(k, r, l, t, e):
  %e : {(k, r) <> l == (k, r) <> _ : List<(String & R)>}
  {==}

def conv.k(k, r, t, w):
  match w:
    case (+G, e1, e2):
      (GCon{k, r, G}, conv.k.eq1(k, r, to_gram(t), G, e1), conv.k.eq2(k, r, from_gram(to_gram(t)), t, e2))

law conv:
  for g: List<(String & R)>
  ConvW(g)

def conv(g):
  match g:
    case Nil{}:
      (GNil{}, {==}, {==})
    case Con{(+k, +r), t}:
      conv.k(k, r, t, conv(t))

law conv.rt.k:
  for -g: List<(String & R)>
  for w: ConvW(g)
  {from_gram(to_gram(g)) == g : List<(String & R)>}

def conv.rt.k(g, w):
  match w:
    case (G, e1, e2):
      e2

law lookup.ok.k:
  for -g: List<(String & L.Rule)>
  for +name: String
  for +book: L.Book
  for +s: String
  for w: ConvW(g)
  {from_gram(to_gram(g)) == g : List<(String & L.Rule)>} & {name == name : String} & {L.check.era(book, L.lookup.era(g, name), s) == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), g) : Bool}

def lookup.ok.k(g, name, book, s, w):
  match w:
    case (+G, +e1, +e2):
      (e2, {==}, lk.any.at(g, G, name, book, s, fg.eq(g, G, e1, e2)))

def L.lookup.ok(g, name, g2, name2, r, h, book, s):
  %h : {Pair.fst(List<(String & L.Rule)>, String & L.Rule, _) == g : List<(String & L.Rule)>} & {Pair.fst(String, L.Rule, Pair.snd(List<(String & L.Rule)>, String & L.Rule, _)) == name : String} & {L.check.era(book, Pair.snd(String, L.Rule, Pair.snd(List<(String & L.Rule)>, String & L.Rule, _)), s) == List.any(~&1, ~(String & L.Rule), ~(m => String.eq(String.to_lower(Pair.fst(String, L.Rule, m)), String.to_lower(name)) && L.check.era(book, Pair.snd(String, L.Rule, m), s)), g) : Bool}
  lookup.ok.k(g, name, book, s, conv(g))

law pf.matches.era.sound:
  for g: List<(String & L.Rule)>
  for name: String
  for s: String
  {L.matches(g, name, s) == (g, name, s, L.matches.era(g, name, s)) : List<(String & L.Rule)> & String & String & Bool}

def pf.matches.era.sound(g, name, s):
  %conv.rt.k(g, conv(g)) : {L.matches(g, name, s) == (_, name, s, L.matches.era(g, name, s)) : List<(String & R)> & String & String & Bool}
  {==}

def L.matches.ok(g, name, s, g2, name2, s2, val, h):
  %Equal.trans(List<(String & R)> & String & String & Bool, (g2, name2, s2, val), L.matches(g, name, s), (g, name, s, L.matches.era(g, name, s)), Equal.sym(List<(String & R)> & String & String & Bool, L.matches(g, name, s), (g2, name2, s2, val), h), pf.matches.era.sound(g, name, s)) : {g2 == Pair.fst(List<(String & R)>, String & String & Bool, _) : List<(String & R)>} & {name2 == Pair.fst(String, String & Bool, Pair.snd(List<(String & R)>, String & String & Bool, _)) : String} & {s2 == Pair.fst(String, Bool, Pair.snd(String, String & Bool, Pair.snd(List<(String & R)>, String & String & Bool, _))) : String} & {val == Pair.snd(String, Bool, Pair.snd(String, String & Bool, Pair.snd(List<(String & R)>, String & String & Bool, _))) : Bool}
  ({==}, {==}, {==}, {==})

def L.matches.era.ok(g, name, s, g2, name2, s2, val, h):
  %Equal.trans(List<(String & R)> & String & String & Bool, (g2, name2, s2, val), L.matches(g, name, s), (g, name, s, L.matches.era(g, name, s)), Equal.sym(List<(String & R)> & String & String & Bool, L.matches(g, name, s), (g2, name2, s2, val), h), pf.matches.era.sound(g, name, s)) : {val == Pair.snd(String, Bool, Pair.snd(String, String & Bool, Pair.snd(List<(String & R)>, String & String & Bool, _))) : Bool}
  {==}

def L.empty():
  Emp{}

law C.empty.nil:
  for book: L.Book
  {ck(book, L.empty, SNil{}) == True{} : Bool}

def C.empty.nil(book):
  {==}

def L.empty.nil(book):
  +book__ = book
  %run.sym(book__, L.empty, SNil{}) : {_ == True{} : Bool}
  C.empty.nil(book__)

law C.empty.con:
  for book: L.Book
  for a: Char
  for t: String
  {ck(book, L.empty, SCon{a, t}) == False{} : Bool}

def C.empty.con(book, a, t):
  {==}

def L.empty.con(book, a, t):
  +book__ = book
  +a__ = a
  +t__ = t
  %run.sym(book__, L.empty, SCon{a__, t__}) : {_ == False{} : Bool}
  C.empty.con(book__, a__, t__)

def L.char(c):
  Lit{c}

law C.char.nil:
  for book: L.Book
  for c: Char
  {ck(book, L.char(c), SNil{}) == False{} : Bool}

def C.char.nil(book, c):
  {==}

def L.char.nil(book, c):
  +book__ = book
  +c__ = c
  %run.sym(book__, L.char(c__), SNil{}) : {_ == False{} : Bool}
  C.char.nil(book__, c__)

law C.char.one:
  for book: L.Book
  for c: Char
  for x: Char
  {ck(book, L.char(c), SCon{x, SNil{}}) == Char.is_eq(c, x) : Bool}

def C.char.one(book, c, x):
  {==}

def L.char.one(book, c, x):
  +book__ = book
  +c__ = c
  +x__ = x
  %run.sym(book__, L.char(c__), SCon{x__, SNil{}}) : {_ == Char.is_eq(c, x) : Bool}
  C.char.one(book__, c__, x__)

law C.char.many:
  for book: L.Book
  for c: Char
  for a: Char
  for b: Char
  for t: String
  {ck(book, L.char(c), SCon{a, SCon{b, t}}) == False{} : Bool}

def C.char.many(book, c, a, b, t):
  {==}

def L.char.many(book, c, a, b, t):
  +book__ = book
  +c__ = c
  +a__ = a
  +b__ = b
  +t__ = t
  %run.sym(book__, L.char(c__), SCon{a__, SCon{b__, t__}}) : {_ == False{} : Bool}
  C.char.many(book__, c__, a__, b__, t__)

def L.seq(rs):
  match rs:
    case Nil{}:
      Emp{}
    case Con{r, t}:
      Cat{r, L.seq(t)}

law C.seq.nil:
  for book: L.Book
  for s: String
  {ck(book, L.seq([]), s) == ck(book, L.empty, s) : Bool}

def C.seq.nil(book, s):
  {==}

def L.seq.nil(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.seq([]), s__) : {_ == L.check.era(book, L.empty, s) : Bool}
  %run.sym(book__, L.empty, s__) : {ck(book, L.seq([]), s) == _ : Bool}
  C.seq.nil(book__, s__)

def L.seq.con.intro(book, r, rs, s1, s2, h1, h2):
  +b = book
  +r2 = r
  +q = L.seq(rs)
  +x = s1
  +y = s2
  from.ck(b, Cat{r2, q}, x ++ y, cat.intro(1n+fuel(b, x ++ y), gram(b), r2, q, x, y, "", lift(b, x, x ++ y, "", y, {==}, r2, to.ck(b, r2, x, h1)), lift(b, y, x ++ y, x, "", app.nil.right(x, y), q, to.ck(b, q, y, h2))))

law seq.con.elim.k:
  for +b: Bk
  for +x: String
  for +r: R
  for +q: R
  for w: CatW(1n+fuel(b, x), gram(b), r, q, x, "")
  exs s1: String
  exs s2: String
  {s1 ++ s2 == x : String} & T(check.run(b, r, s1)) & T(check.run(b, q, s2))

def seq.con.elim.k(b, x, r, q, w):
  match w:
    case (+s1, +s2, e, ha, hb):
      (s1, s2, e, from.ck(b, r, s1, lower(b, x, s1, r, ha)), from.ck(b, q, s2, lower(b, x, s2, q, hb)))

def L.seq.con.elim(book, r, rs, s, h):
  +b = book
  +r2 = r
  +q = L.seq(rs)
  +x = s
  seq.con.elim.k(b, x, r2, q, cat.elim(1n+fuel(b, x), gram(b), r2, q, x, "", to.ck(b, Cat{r2, q}, x, h)))

def L.alt(rs):
  match rs:
    case Nil{}:
      Bad{}
    case Con{r, t}:
      Alt{r, L.alt(t)}

law C.alt.nil:
  for book: L.Book
  for s: String
  {ck(book, L.alt([]), s) == False{} : Bool}

def C.alt.nil(book, s):
  {==}

def L.alt.nil(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.alt([]), s__) : {_ == False{} : Bool}
  C.alt.nil(book__, s__)

def L.alt.con(book, s, r, rs):
  +b = book
  +x = s
  +r2 = r
  +q = L.alt(rs)
  %run.sym(b, Alt{r2, q}, x) : {_ == L.check.era(book, r, s) || L.check.era(book, L.alt(rs), s) : Bool}
  %run.sym(b, r2, x) : {ck(b, Alt{r2, q}, x) == _ || L.check.era(book, L.alt(rs), s) : Bool}
  %run.sym(b, q, x) : {ck(b, Alt{r2, q}, x) == ck(b, r2, x) || _ : Bool}
  or.eq(sem(1n+fuel(b, x), gram(b), r2, x, ""), sem(1n+fuel(b, x), gram(b), q, x, ""))

def chars.go(n: Nat, +c: Char) -> List<R>:
  match n:
    case 0n:
      []
    case 1n+m:
      Lit{c} <> chars.go(m, Chr{(Char.to_u32(c) + 1 : U32)})

def L.chars(n, c):
  chars.go(n, c)

def L.chars.nil(c):
  {==}

def L.chars.con(c, n):
  {==}

law nat.le0:
  for m: Nat
  T(Nat.is_le(0n, m))

def nat.le0(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

law nat.sub.le:
  for H: Nat
  for A: Nat
  for -m: Nat
  for h: {1n+m == Nat.sub(1n+H, A) : Nat}
  T(Nat.is_le(A, H))

def nat.sub.le(H, A, m, h):
  match H A:
    case _ 0n:
      nat.le0(H)
    case 0n 1n+a:
      absurd(T(Nat.is_le(1n+a, 0n)), succ.empty(m, h))
    case 1n+q 1n+a:
      nat.sub.le(q, a, m, h)

law nat.sub.succ:
  for H: Nat
  for A: Nat
  for h: T(Nat.is_le(A, H))
  {1n+Nat.sub(H, A) == Nat.sub(1n+H, A) : Nat}

def nat.sub.succ(H, A, h):
  match H A:
    case 0n 0n:
      {==}
    case 1n+q 0n:
      {==}
    case 0n 1n+a:
      false.elim({1n+Nat.sub(0n, 1n+a) == Nat.sub(1n, 1n+a) : Nat}, h)
    case 1n+q 1n+a:
      nat.sub.succ(q, a, h)

law and.false:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def and.false(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def isleN(A: Nat, +X: Nat, H: Nat) -> Bool:
  Bool.and(Nat.is_le(A, X), Nat.is_le(X, H))

law nat.nope:
  for A: Nat
  for X: Nat
  for H: Nat
  for h: {0n == Nat.sub(1n+H, A) : Nat}
  {False{} == isleN(A, X, H) : Bool}

def nat.nope(A, X, H, h):
  match A X H:
    case 0n _ _:
      absurd({False{} == isleN(0n, X, H) : Bool}, succ.empty(H, Equal.sym(Nat, 0n, 1n+H, h)))
    case 1n+a 0n _:
      {==}
    case 1n+a 1n+x 0n:
      Equal.sym(Bool, Bool.and(Nat.is_le(a, x), False{}), False{}, and.false(Nat.is_le(a, x)))
    case 1n+a 1n+x 1n+y:
      nat.nope(a, x, y, h)

law nat.split.le:
  for +A: Nat
  for +X: Nat
  for +H: Nat
  for hle: T(Nat.is_le(A, H))
  {orelse(Nat.is_eq(A, X), u => isleN(1n+A, X, H)) == isleN(A, X, H) : Bool}

def nat.split.le(A, X, H, hle):
  match A X H:
    case 0n 0n _:
      Equal.sym(Bool, Nat.is_le(0n, H), True{}, nat.le0(H))
    case 0n 1n+x _:
      %Equal.sym(Bool, Nat.is_le(0n, x), True{}, nat.le0(x)) : {Bool.and(_, Nat.is_le(1n+x, H)) == Nat.is_le(1n+x, H) : Bool}
      {==}
    case 1n+a 0n _:
      {==}
    case 1n+a 1n+x 0n:
      false.elim({orelse(Nat.is_eq(1n+a, 1n+x), u => isleN(2n+a, 1n+x, 0n)) == isleN(1n+a, 1n+x, 0n) : Bool}, hle)
    case 1n+a 1n+x 1n+y:
      nat.split.le(a, x, y, hle)

law succ.inj:
  for -a: Nat
  for -b: Nat
  for h: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ.inj(a, b, h):
  %h : {a == succ.pred(_) : Nat}
  {==}

law chain.nil:
  for n: Nat
  for +e: Nat
  for -g: Gram
  for +u: U32
  {sem(1n+e, g, L.alt(chars.go(n, Chr{u})), "", "") == False{} : Bool}

def chain.nil(n, e, g, u):
  match n:
    case 0n:
      {==}
    case 1n+m:
      chain.nil(m, e, g, (u + 1 : U32))

law chain.many:
  for n: Nat
  for +e: Nat
  for -g: Gram
  for +u: U32
  for -a: Char
  for -b: Char
  for -t: String
  {sem(1n+e, g, L.alt(chars.go(n, Chr{u})), SCon{a, SCon{b, t}}, "") == False{} : Bool}

def chain.many(n, e, g, u, a, b, t):
  match n:
    case 0n:
      {==}
    case 1n+m:
      chain.many(m, e, g, (u + 1 : U32), a, b, t)

law chain.step:
  for +u: U32
  for +x: U32
  for +H: U32
  for -S: Bool
  for hs: {isleN(1n+N(u), N(x), N(H)) == S : Bool}
  for hle: T(Nat.is_le(N(u), N(H)))
  {orelse(U32.is_eq(u, x), v => S) == isle(u, x, H) : Bool}

def chain.step(u, x, H, S, hs, hle):
  %hs : {orelse(U32.is_eq(u, x), v => _) == isle(u, x, H) : Bool}
  %u32.eq.nat(u, x) : {orelse(_, v => isleN(1n+N(u), N(x), N(H))) == isle(u, x, H) : Bool}
  %u32.le.nat(u, x) : {orelse(Nat.is_eq(N(u), N(x)), v => isleN(1n+N(u), N(x), N(H))) == Bool.and(_, U32.is_le(x, H)) : Bool}
  %u32.le.nat(x, H) : {orelse(Nat.is_eq(N(u), N(x)), v => isleN(1n+N(u), N(x), N(H))) == Bool.and(Nat.is_le(N(u), N(x)), _) : Bool}
  nat.split.le(N(u), N(x), N(H), hle)

law chain.tail:
  for +u: U32
  for +x: U32
  for +H: U32
  for -S: Bool
  for e1: {1n+N(u) == N(U32.add(u, 1)) : Nat}
  for ih: {S == isle(U32.add(u, 1), x, H) : Bool}
  {isleN(1n+N(u), N(x), N(H)) == S : Bool}

def chain.tail(u, x, H, S, e1, ih):
  %Equal.sym(Bool, S, isle(U32.add(u, 1), x, H), ih) : {isleN(1n+N(u), N(x), N(H)) == _ : Bool}
  %u32.le.nat(x, H) : {isleN(1n+N(u), N(x), N(H)) == Bool.and(U32.is_le(U32.add(u, 1), x), _) : Bool}
  %u32.le.nat(U32.add(u, 1), x) : {isleN(1n+N(u), N(x), N(H)) == Bool.and(_, Nat.is_le(N(x), N(H))) : Bool}
  %e1 : {isleN(1n+N(u), N(x), N(H)) == Bool.and(Nat.is_le(_, N(x)), Nat.is_le(N(x), N(H))) : Bool}
  {==}

law chain.h1:
  for -q: Nat
  for -u: U32
  for -H: U32
  for e1: {1n+N(u) == N(U32.add(u, 1)) : Nat}
  for h0: {1n+q == Nat.sub(N(H), N(u)) : Nat}
  {1n+q == Nat.sub(1n+N(H), N(U32.add(u, 1))) : Nat}

def chain.h1(q, u, H, e1, h0):
  %e1 : {1n+q == Nat.sub(1n+N(H), _) : Nat}
  h0

law chain.pred:
  for -k: Nat
  for -H: Nat
  for -A: Nat
  for h: {1n+k == Nat.sub(1n+H, A) : Nat}
  for s: {1n+Nat.sub(H, A) == Nat.sub(1n+H, A) : Nat}
  {k == Nat.sub(H, A) : Nat}

def chain.pred(k, H, A, h, s):
  succ.inj(k, Nat.sub(H, A), Equal.trans(Nat, 1n+k, Nat.sub(1n+H, A), 1n+Nat.sub(H, A), h, Equal.sym(Nat, 1n+Nat.sub(H, A), Nat.sub(1n+H, A), s)))

law chain.one:
  for +n: Nat
  for +e: Nat
  for +g: Gram
  for +u: U32
  for +x: U32
  for +H: U32
  for +h: {n == Nat.sub(1n+N(H), N(u)) : Nat}
  {sem(1n+e, g, L.alt(chars.go(n, Chr{u})), SCon{Chr{x}, SNil{}}, "") == isle(u, x, H) : Bool}

def chain.one(n, e, g, u, x, H, h):
  match n:
    case 0n:
      %u32.le.nat(u, x) : {False{} == Bool.and(_, U32.is_le(x, H)) : Bool}
      %u32.le.nat(x, H) : {False{} == Bool.and(Nat.is_le(N(u), N(x)), _) : Bool}
      nat.nope(N(u), N(x), N(H), h)
    case 1n+m:
      match m:
        case 0n:
          chain.step(u, x, H, False{}, Equal.sym(Bool, False{}, isleN(1n+N(u), N(x), N(H)), nat.nope(1n+N(u), N(x), N(H), chain.pred(0n, N(H), N(u), h, nat.sub.succ(N(H), N(u), nat.sub.le(N(H), N(u), 0n, h))))), nat.sub.le(N(H), N(u), 0n, h))
        case 1n+q:
          chain.step(u, x, H, sem(1n+e, g, L.alt(chars.go(m, Chr{U32.add(u, 1)})), SCon{Chr{x}, SNil{}}, ""), chain.tail(u, x, H, sem(1n+e, g, L.alt(chars.go(m, Chr{U32.add(u, 1)})), SCon{Chr{x}, SNil{}}, ""), u32.succ.nat(u, H, nat.sub.le(N(H), 1n+N(u), q, chain.pred(1n+q, N(H), N(u), h, nat.sub.succ(N(H), N(u), nat.sub.le(N(H), N(u), 1n+q, h))))), chain.one(m, e, g, U32.add(u, 1), x, H, chain.h1(q, u, H, u32.succ.nat(u, H, nat.sub.le(N(H), 1n+N(u), q, chain.pred(1n+q, N(H), N(u), h, nat.sub.succ(N(H), N(u), nat.sub.le(N(H), N(u), 1n+q, h))))), chain.pred(1n+q, N(H), N(u), h, nat.sub.succ(N(H), N(u), nat.sub.le(N(H), N(u), 1n+q, h)))))), nat.sub.le(N(H), N(u), 1n+q, h))

law range.eq:
  for start: Char
  for end: Char
  for +e: Nat
  for +g: Gram
  for s: String
  {sem(1n+e, g, Rng{Char.to_u32(start), Char.to_u32(end)}, s, "") == sem(1n+e, g, L.alt(chars.go(Nat.sub(1n+U32.to_nat(Char.to_u32(end)), U32.to_nat(Char.to_u32(start))), start)), s, "") : Bool}

def range.eq(start, end, e, g, s):
  match start end:
    case Chr{+u} Chr{+H}:
      match s:
        case SNil{}:
          Equal.sym(Bool, sem(1n+e, g, L.alt(chars.go(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), Chr{u})), "", ""), False{}, chain.nil(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), e, g, u))
        case SCon{Chr{+x}, SNil{}}:
          Equal.sym(Bool, sem(1n+e, g, L.alt(chars.go(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), Chr{u})), SCon{Chr{x}, SNil{}}, ""), isle(u, x, H), chain.one(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), e, g, u, x, H, {==}))
        case SCon{a, SCon{b, t2}}:
          Equal.sym(Bool, sem(1n+e, g, L.alt(chars.go(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), Chr{u})), SCon{a, SCon{b, t2}}, ""), False{}, chain.many(Nat.sub(1n+U32.to_nat(H), U32.to_nat(u)), e, g, u, a, b, t2))

def L.range(start, end):
  Rng{Char.to_u32(start), Char.to_u32(end)}

law C.range.ok:
  for book: L.Book
  for start: Char
  for end: Char
  for s: String
  {ck(book, L.range(start, end), s) == ck(book, L.alt(L.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(end)), U32.to_nat(Char.to_u32(start))), start)), s) : Bool}

def C.range.ok(book, start, end, s):
  +b = book
  +x = s
  range.eq(start, end, fuel(b, x), gram(b), x)

def L.range.ok(book, start, end, s):
  +book__ = book
  +start__ = start
  +end__ = end
  +s__ = s
  %run.sym(book__, L.range(start__, end__), s__) : {_ == L.check.era(book, L.alt(L.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(end)), U32.to_nat(Char.to_u32(start))), start)), s) : Bool}
  %run.sym(book__, L.alt(L.chars(Nat.sub(1n+U32.to_nat(Char.to_u32(end__)), U32.to_nat(Char.to_u32(start__))), start__)), s__) : {ck(book, L.range(start, end), s) == _ : Bool}
  C.range.ok(book__, start__, end__, s__)

def L.string.case_sensitive(lit):
  match lit:
    case SNil{}:
      Emp{}
    case SCon{c, t}:
      L.seq([L.char(c), L.string.case_sensitive(t)])

law C.string.case_sensitive.nil:
  for book: L.Book
  for s: String
  {ck(book, L.string.case_sensitive(SNil{}), s) == ck(book, L.empty, s) : Bool}

def C.string.case_sensitive.nil(book, s):
  {==}

def L.string.case_sensitive.nil(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.string.case_sensitive(SNil{}), s__) : {_ == L.check.era(book, L.empty, s) : Bool}
  %run.sym(book__, L.empty, s__) : {ck(book, L.string.case_sensitive(SNil{}), s) == _ : Bool}
  C.string.case_sensitive.nil(book__, s__)

law C.string.case_sensitive.con:
  for book: L.Book
  for c: Char
  for t: String
  for s: String
  {ck(book, L.string.case_sensitive(SCon{c, t}), s) == ck(book, L.seq([L.char(c), L.string.case_sensitive(t)]), s) : Bool}

def C.string.case_sensitive.con(book, c, t, s):
  {==}

def L.string.case_sensitive.con(book, s, c, t):
  +book__ = book
  +c__ = c
  +t__ = t
  +s__ = s
  %run.sym(book__, L.string.case_sensitive(SCon{c__, t__}), s__) : {_ == L.check.era(book, L.seq([L.char(c), L.string.case_sensitive(t)]), s) : Bool}
  %run.sym(book__, L.seq([L.char(c__), L.string.case_sensitive(t__)]), s__) : {ck(book, L.string.case_sensitive(SCon{c, t}), s) == _ : Bool}
  C.string.case_sensitive.con(book__, c__, t__, s__)

def L.string.case_insensitive(lit):
  match lit:
    case SNil{}:
      Emp{}
    case SCon{+c, t}:
      L.seq([L.alt([L.char(Char.to_lower(c)), L.char(Char.to_upper(c))]), L.string.case_insensitive(t)])

law C.string.case_insensitive.nil:
  for book: L.Book
  for s: String
  {ck(book, L.string.case_insensitive(SNil{}), s) == ck(book, L.empty, s) : Bool}

def C.string.case_insensitive.nil(book, s):
  {==}

def L.string.case_insensitive.nil(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.string.case_insensitive(SNil{}), s__) : {_ == L.check.era(book, L.empty, s) : Bool}
  %run.sym(book__, L.empty, s__) : {ck(book, L.string.case_insensitive(SNil{}), s) == _ : Bool}
  C.string.case_insensitive.nil(book__, s__)

law C.string.case_insensitive.con:
  for book: L.Book
  for c: Char
  for t: String
  for s: String
  {ck(book, L.string.case_insensitive(SCon{c, t}), s) == ck(book, L.seq([L.alt([L.char(Char.to_lower(c)), L.char(Char.to_upper(c))]), L.string.case_insensitive(t)]), s) : Bool}

def C.string.case_insensitive.con(book, c, t, s):
  {==}

def L.string.case_insensitive.con(book, s, c, t):
  +book__ = book
  +c__ = c
  +t__ = t
  +s__ = s
  %run.sym(book__, L.string.case_insensitive(SCon{c__, t__}), s__) : {_ == L.check.era(book, L.seq([L.alt([L.char(Char.to_lower(c)), L.char(Char.to_upper(c))]), L.string.case_insensitive(t)]), s) : Bool}
  %run.sym(book__, L.seq([L.alt([L.char(Char.to_lower(c__)), L.char(Char.to_upper(c__))]), L.string.case_insensitive(t__)]), s__) : {ck(book, L.string.case_insensitive(SCon{c, t}), s) == _ : Bool}
  C.string.case_insensitive.con(book__, c__, t__, s__)

def L.rep.exactly(n, r):
  exact(n, r)

law C.rep.exactly.zero:
  for book: L.Book
  for r: L.Rule
  for s: String
  {ck(book, L.rep.exactly(0n, r), s) == ck(book, L.empty, s) : Bool}

def C.rep.exactly.zero(book, r, s):
  {==}

def L.rep.exactly.zero(book, r, s):
  +book__ = book
  +r__ = r
  +s__ = s
  %run.sym(book__, L.rep.exactly(0n, r__), s__) : {_ == L.check.era(book, L.empty, s) : Bool}
  %run.sym(book__, L.empty, s__) : {ck(book, L.rep.exactly(0n, r), s) == _ : Bool}
  C.rep.exactly.zero(book__, r__, s__)

law C.rep.exactly.succ:
  for book: L.Book
  for n: Nat
  for r: L.Rule
  for s: String
  {ck(book, L.rep.exactly(1n+n, r), s) == ck(book, L.seq([r, L.rep.exactly(n, r)]), s) : Bool}

def C.rep.exactly.succ(book, n, r, s):
  {==}

def L.rep.exactly.succ(book, r, s, n):
  +book__ = book
  +n__ = n
  +r__ = r
  +s__ = s
  %run.sym(book__, L.rep.exactly(1n+n__, r__), s__) : {_ == L.check.era(book, L.seq([r, L.rep.exactly(n, r)]), s) : Bool}
  %run.sym(book__, L.seq([r__, L.rep.exactly(n__, r__)]), s__) : {ck(book, L.rep.exactly(1n+n, r), s) == _ : Bool}
  C.rep.exactly.succ(book__, n__, r__, s__)

def L.rep.any(r):
  Star{r}

def L.rep.any.intro(book, m, r, s, hs):
  +b = book
  +m2 = m
  +r2 = r
  +x = s
  from.ck(b, Star{r2}, x, star.intro(m2, 1n+fuel(b, x), gram(b), r2, x, to.ck(b, exact(m2, r2), x, hs)))

def L.rep.any.elim(book, r, s, hs):
  +b = book
  +r2 = r
  +x = s
  any.k(b, x, r2, star.elim(1n+fuel(b, x), gram(b), r2, x, "", to.ck(b, Star{r2}, x, hs)))

def L.rep.at_least(n, r):
  atl(n, r)

def L.rep.at_least.intro(book, n, m, h, r, s, hs):
  +b = book
  +n2 = n
  +m2 = m
  +r2 = r
  +x = s
  from.ck(b, atl(n2, r2), x, atl.intro(n2, m2, h, 1n+fuel(b, x), gram(b), r2, x, to.ck(b, exact(m2, r2), x, hs)))

def L.rep.at_least.elim(book, n, r, s, hs):
  +b = book
  +n2 = n
  +r2 = r
  +x = s
  atl.fix(b, x, r2, n2, atl.elim(n2, 1n+fuel(b, x), gram(b), r2, x, to.ck(b, atl(n2, r2), x, hs)))

def L.rep(a, b, r):
  rpt(a, b, r)

def L.rep.intro(book, a, b, m, ha, hb, r, s, hs):
  +bk = book
  +a2 = a
  +b2 = b
  +m2 = m
  +r2 = r
  +x = s
  from.ck(bk, rpt(a2, b2, r2), x, rpt.intro(a2, b2, m2, ha, hb, 1n+fuel(bk, x), gram(bk), r2, x, to.ck(bk, exact(m2, r2), x, hs)))

def L.rep.elim(book, a, b, r, s, hs):
  +bk = book
  +a2 = a
  +b2 = b
  +r2 = r
  +x = s
  rpt.fix(bk, x, r2, a2, b2, rpt.elim(a2, b2, 1n+fuel(bk, x), gram(bk), r2, x, to.ck(bk, rpt(a2, b2, r2), x, hs)))

def L.rep.at_most(n, r):
  L.rep(0n, n, r)

def L.rep.at_most.intro(book, n, m, h, r, s, hs):
  +bk = book
  +n2 = n
  +m2 = m
  +r2 = r
  +x = s
  from.ck(bk, rpt(0n, n2, r2), x, rpt.intro(0n, n2, m2, le0(m2), h, 1n+fuel(bk, x), gram(bk), r2, x, to.ck(bk, exact(m2, r2), x, hs)))

def L.rep.at_most.elim(book, n, r, s, hs):
  +bk = book
  +n2 = n
  +r2 = r
  +x = s
  atm.fix(bk, x, r2, n2, rpt.elim(0n, n2, 1n+fuel(bk, x), gram(bk), r2, x, to.ck(bk, rpt(0n, n2, r2), x, hs)))

def L.opt(r):
  L.alt([L.empty, r])

law C.opt.ok:
  for book: L.Book
  for r: L.Rule
  for s: String
  {ck(book, L.opt(r), s) == ck(book, L.alt([L.empty, r]), s) : Bool}

def C.opt.ok(book, r, s):
  {==}

def L.opt.ok(book, r, s):
  +book__ = book
  +r__ = r
  +s__ = s
  %run.sym(book__, L.opt(r__), s__) : {_ == L.check.era(book, L.alt([L.empty, r]), s) : Bool}
  %run.sym(book__, L.alt([L.empty, r__]), s__) : {ck(book, L.opt(r), s) == _ : Bool}
  C.opt.ok(book__, r__, s__)

def L.core.alpha():
  L.alt([L.range('A', 'Z'), L.range('a', 'z')])

law C.core.alpha.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.alpha, s) == ck(book, L.alt([L.range('A', 'Z'), L.range('a', 'z')]), s) : Bool}

def C.core.alpha.ok(book, s):
  {==}

def L.core.alpha.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.alpha, s__) : {_ == L.check.era(book, L.alt([L.range('A', 'Z'), L.range('a', 'z')]), s) : Bool}
  %run.sym(book__, L.alt([L.range('A', 'Z'), L.range('a', 'z')]), s__) : {ck(book, L.core.alpha, s) == _ : Bool}
  C.core.alpha.ok(book__, s__)

def L.core.bit():
  L.alt([L.string.case_insensitive("0"), L.string.case_insensitive("1")])

law C.core.bit.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.bit, s) == ck(book, L.alt([L.string.case_insensitive("0"), L.string.case_insensitive("1")]), s) : Bool}

def C.core.bit.ok(book, s):
  {==}

def L.core.bit.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.bit, s__) : {_ == L.check.era(book, L.alt([L.string.case_insensitive("0"), L.string.case_insensitive("1")]), s) : Bool}
  %run.sym(book__, L.alt([L.string.case_insensitive("0"), L.string.case_insensitive("1")]), s__) : {ck(book, L.core.bit, s) == _ : Bool}
  C.core.bit.ok(book__, s__)

def L.core.char():
  L.range(Chr{1}, Chr{127})

law C.core.char.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.char, s) == ck(book, L.range(Chr{1}, Chr{127}), s) : Bool}

def C.core.char.ok(book, s):
  {==}

def L.core.char.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.char, s__) : {_ == L.check.era(book, L.range(Chr{1}, Chr{127}), s) : Bool}
  %run.sym(book__, L.range(Chr{1}, Chr{127}), s__) : {ck(book, L.core.char, s) == _ : Bool}
  C.core.char.ok(book__, s__)

def L.core.cr():
  L.char('\r')

law C.core.cr.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.cr, s) == ck(book, L.char('\r'), s) : Bool}

def C.core.cr.ok(book, s):
  {==}

def L.core.cr.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.cr, s__) : {_ == L.check.era(book, L.char('\r'), s) : Bool}
  %run.sym(book__, L.char('\r'), s__) : {ck(book, L.core.cr, s) == _ : Bool}
  C.core.cr.ok(book__, s__)

def L.core.lf():
  L.char('\n')

law C.core.lf.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.lf, s) == ck(book, L.char('\n'), s) : Bool}

def C.core.lf.ok(book, s):
  {==}

def L.core.lf.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.lf, s__) : {_ == L.check.era(book, L.char('\n'), s) : Bool}
  %run.sym(book__, L.char('\n'), s__) : {ck(book, L.core.lf, s) == _ : Bool}
  C.core.lf.ok(book__, s__)

def L.core.crlf():
  L.seq([L.core.cr, L.core.lf])

law C.core.crlf.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.crlf, s) == ck(book, L.seq([L.core.cr, L.core.lf]), s) : Bool}

def C.core.crlf.ok(book, s):
  {==}

def L.core.crlf.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.crlf, s__) : {_ == L.check.era(book, L.seq([L.core.cr, L.core.lf]), s) : Bool}
  %run.sym(book__, L.seq([L.core.cr, L.core.lf]), s__) : {ck(book, L.core.crlf, s) == _ : Bool}
  C.core.crlf.ok(book__, s__)

def L.core.ctl():
  L.alt([L.range(Chr{0}, Chr{31}), L.char(Chr{127})])

law C.core.ctl.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.ctl, s) == ck(book, L.alt([L.range(Chr{0}, Chr{31}), L.char(Chr{127})]), s) : Bool}

def C.core.ctl.ok(book, s):
  {==}

def L.core.ctl.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.ctl, s__) : {_ == L.check.era(book, L.alt([L.range(Chr{0}, Chr{31}), L.char(Chr{127})]), s) : Bool}
  %run.sym(book__, L.alt([L.range(Chr{0}, Chr{31}), L.char(Chr{127})]), s__) : {ck(book, L.core.ctl, s) == _ : Bool}
  C.core.ctl.ok(book__, s__)

def L.core.digit():
  L.range('0', '9')

law C.core.digit.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.digit, s) == ck(book, L.range('0', '9'), s) : Bool}

def C.core.digit.ok(book, s):
  {==}

def L.core.digit.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.digit, s__) : {_ == L.check.era(book, L.range('0', '9'), s) : Bool}
  %run.sym(book__, L.range('0', '9'), s__) : {ck(book, L.core.digit, s) == _ : Bool}
  C.core.digit.ok(book__, s__)

def L.core.dquote():
  L.char('"')

law C.core.dquote.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.dquote, s) == ck(book, L.char('"'), s) : Bool}

def C.core.dquote.ok(book, s):
  {==}

def L.core.dquote.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.dquote, s__) : {_ == L.check.era(book, L.char('"'), s) : Bool}
  %run.sym(book__, L.char('"'), s__) : {ck(book, L.core.dquote, s) == _ : Bool}
  C.core.dquote.ok(book__, s__)

def L.core.hexdig():
  L.alt([L.core.digit, L.string.case_insensitive("A"), L.string.case_insensitive("B"), L.string.case_insensitive("C"), L.string.case_insensitive("D"), L.string.case_insensitive("E"), L.string.case_insensitive("F")])

law C.core.hexdig.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.hexdig, s) == ck(book, L.alt([L.core.digit, L.string.case_insensitive("A"), L.string.case_insensitive("B"), L.string.case_insensitive("C"), L.string.case_insensitive("D"), L.string.case_insensitive("E"), L.string.case_insensitive("F")]), s) : Bool}

def C.core.hexdig.ok(book, s):
  {==}

def L.core.hexdig.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.hexdig, s__) : {_ == L.check.era(book, L.alt([L.core.digit, L.string.case_insensitive("A"), L.string.case_insensitive("B"), L.string.case_insensitive("C"), L.string.case_insensitive("D"), L.string.case_insensitive("E"), L.string.case_insensitive("F")]), s) : Bool}
  %run.sym(book__, L.alt([L.core.digit, L.string.case_insensitive("A"), L.string.case_insensitive("B"), L.string.case_insensitive("C"), L.string.case_insensitive("D"), L.string.case_insensitive("E"), L.string.case_insensitive("F")]), s__) : {ck(book, L.core.hexdig, s) == _ : Bool}
  C.core.hexdig.ok(book__, s__)

def L.core.htab():
  L.char('\t')

law C.core.htab.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.htab, s) == ck(book, L.char('\t'), s) : Bool}

def C.core.htab.ok(book, s):
  {==}

def L.core.htab.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.htab, s__) : {_ == L.check.era(book, L.char('\t'), s) : Bool}
  %run.sym(book__, L.char('\t'), s__) : {ck(book, L.core.htab, s) == _ : Bool}
  C.core.htab.ok(book__, s__)

def L.core.sp():
  L.char(' ')

law C.core.sp.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.sp, s) == ck(book, L.char(' '), s) : Bool}

def C.core.sp.ok(book, s):
  {==}

def L.core.sp.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.sp, s__) : {_ == L.check.era(book, L.char(' '), s) : Bool}
  %run.sym(book__, L.char(' '), s__) : {ck(book, L.core.sp, s) == _ : Bool}
  C.core.sp.ok(book__, s__)

def L.core.wsp():
  L.alt([L.core.sp, L.core.htab])

law C.core.wsp.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.wsp, s) == ck(book, L.alt([L.core.sp, L.core.htab]), s) : Bool}

def C.core.wsp.ok(book, s):
  {==}

def L.core.wsp.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.wsp, s__) : {_ == L.check.era(book, L.alt([L.core.sp, L.core.htab]), s) : Bool}
  %run.sym(book__, L.alt([L.core.sp, L.core.htab]), s__) : {ck(book, L.core.wsp, s) == _ : Bool}
  C.core.wsp.ok(book__, s__)

def L.core.lwsp():
  L.rep.any(L.alt([L.core.wsp, L.seq([L.core.crlf, L.core.wsp])]))

law C.core.lwsp.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.lwsp, s) == ck(book, L.rep.any(L.alt([L.core.wsp, L.seq([L.core.crlf, L.core.wsp])])), s) : Bool}

def C.core.lwsp.ok(book, s):
  {==}

def L.core.lwsp.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.lwsp, s__) : {_ == L.check.era(book, L.rep.any(L.alt([L.core.wsp, L.seq([L.core.crlf, L.core.wsp])])), s) : Bool}
  %run.sym(book__, L.rep.any(L.alt([L.core.wsp, L.seq([L.core.crlf, L.core.wsp])])), s__) : {ck(book, L.core.lwsp, s) == _ : Bool}
  C.core.lwsp.ok(book__, s__)

def L.core.octet():
  L.range(Chr{0}, Chr{255})

law C.core.octet.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.octet, s) == ck(book, L.range(Chr{0}, Chr{255}), s) : Bool}

def C.core.octet.ok(book, s):
  {==}

def L.core.octet.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.octet, s__) : {_ == L.check.era(book, L.range(Chr{0}, Chr{255}), s) : Bool}
  %run.sym(book__, L.range(Chr{0}, Chr{255}), s__) : {ck(book, L.core.octet, s) == _ : Bool}
  C.core.octet.ok(book__, s__)

def L.core.vchar():
  L.range('!', '~')

law C.core.vchar.ok:
  for book: L.Book
  for s: String
  {ck(book, L.core.vchar, s) == ck(book, L.range('!', '~'), s) : Bool}

def C.core.vchar.ok(book, s):
  {==}

def L.core.vchar.ok(book, s):
  +book__ = book
  +s__ = s
  %run.sym(book__, L.core.vchar, s__) : {_ == L.check.era(book, L.range('!', '~'), s) : Bool}
  %run.sym(book__, L.range('!', '~'), s__) : {ck(book, L.core.vchar, s) == _ : Bool}
  C.core.vchar.ok(book__, s__)
