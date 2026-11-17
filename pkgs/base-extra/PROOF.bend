# Models for base-extra's laws.

import Base
import ./LAWS.bend as Laws

# ====
# Sing
# ====

# Sing, stored as the value with evidence fixing the index.
type SingT<-A: Type, -a: A> is Type:
  SMake{x: A, e: {x == a : A}}

def Laws.Sing(A, a):
  SingT<A, a>

def Laws.Sing.make(A, a):
  SMake{a, {==}}

def Laws.Sing.rec(A, Q, f, a, s):
  match s:
    case SMake{x, e}:
      %e@e : Q(_, SMake{x, e})
      f(x)

def Laws.Sing.rec.make(A, Q, f, a):
  {==}

# ========
# Pair.All
# ========

# Pair.All, stored as both proofs with evidence fixing the index.
type PAllT<-A: Type, -B: Type, -PA: @-x:A -> Type, -PB: @-x:B -> Type, -p: A & B> is Type:
  PMake{-a: A, -b: B, e: {(a, b) == p : A & B}, pa: PA(a), pb: PB(b)}

def Laws.Pair.All(A, B, PA, PB, p):
  PAllT<A, B, PA, PB, p>

def Laws.Pair.All.make(A, B, PA, PB, a, b, pa, pb):
  PMake{a, b, {==}, pa, pb}

def Laws.Pair.All.rec(A, B, PA, PB, Q, f, p, x):
  match x:
    case PMake{a, b, e, pa, pb}:
      %e@e : Q(_, PMake{a, b, e, pa, pb})
      f(a, b, pa, pb)

def Laws.Pair.All.rec.make(A, B, PA, PB, Q, f, a, b, pa, pb):
  {==}

def Laws.Pair.All.of(A, B, PA, PB, fa, fb, p):
  match p:
    case (a, b):
      PMake{a, b, {==}, fa(a), fb(b)}

def Laws.Pair.All.of.make(A, B, PA, PB, fa, fb, a, b):
  {==}

# ========
# List.All
# ========

# List.All, stored as a list of proofs with evidence fixing the index.
type AllT<-A: Type, -P: @-x:A -> Type, -xs: List<A>> is Type:
  ANil{e: {[] == xs : List<A>}}
  ACons{-h: A, -t: List<A>, e: {h <> t == xs : List<A>}, ph: P(h), r: AllT<A, P, t>}

def Laws.List.All(A, P, xs):
  AllT<A, P, xs>

def Laws.List.All.nil(A, P):
  ANil{{==}}

def Laws.List.All.cons(A, P, x, xs, px, rest):
  ACons{x, xs, {==}, px, rest}

def Laws.List.All.rec(A, P, Q, on_nil, on_cons, xs, a):
  match a:
    case ANil{e}:
      %e@e : Q(_, ANil{e})
      on_nil
    case ACons{h, t, e, ph, r}:
      %e@e : Q(_, ACons{h, t, e, ph, r})
      on_cons(h, t, ph, r, Laws.List.All.rec(~A, ~P, ~Q, ~on_nil, ~on_cons, t, r))

def Laws.List.All.rec.nil(A, P, Q, on_nil, on_cons):
  {==}

def Laws.List.All.rec.cons(A, P, Q, on_nil, on_cons, x, xs, px, rest):
  {==}

def Laws.List.All.cases(A, P, Q, on_nil, on_cons, xs, a):
  match a:
    case ANil{e}:
      %e@e : Q(_, ANil{e})
      on_nil
    case ACons{h, t, e, ph, r}:
      %e@e : Q(_, ACons{h, t, e, ph, r})
      on_cons(h, t, ph, r)

def Laws.List.All.cases.nil(A, P, Q, on_nil, on_cons):
  {==}

def Laws.List.All.cases.cons(A, P, Q, on_nil, on_cons, x, xs, px, rest):
  {==}

def Laws.List.All.of(A, P, f, xs):
  match xs:
    case []:
      ANil{{==}}
    case h <> t:
      ACons{h, t, {==}, f(h), Laws.List.All.of(~A, ~P, ~f, t)}

def Laws.List.All.of.nil(A, P, f):
  {==}

def Laws.List.All.of.cons(A, P, f, x, xs):
  {==}

# ======
# String
# ======

# cidx(ds, c, i): i plus the position of c in ds, or 0 when c is absent.
def cidx.if(hit: Bool, i: U32, rest: Unit -> U32) -> U32:
  match hit:
    case True{}:
      i
    case False{}:
      rest(Unit{})

def cidx(ds: String, +c: Char, +i: U32) -> U32:
  match ds:
    case SNil{}:
      0
    case SCon{h, t}:
      cidx.if(Char.is_eq(h, c), i, u => cidx(t, c, (i + 1 : U32)))

# hv(s): the value of the lowercase hexadecimal digit at the head of s.
def hv(s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{c, t}:
      cidx("0123456789abcdef", c, 0)

# dval(d) is the value of the one-digit string d, in either case.
def dval(d: String) -> U32:
  hv(String.to_lower(d))

# hex.go(s, acc): the value of acc followed by the digits s.
def hex.go(s: String, acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      hex.go(t, (acc * 16 + dval(SCon{c, SNil{}}) : U32))

def Laws.String.is_hex.era(s):
  +x = s
  Bool.not(String.is_empty(x)) && List.all(~&2, ~Char, ~(c => String.contains("0123456789abcdefABCDEF", SCon{c, SNil{}})), String.to_list(x))

def Laws.String.is_hex(s):
  +x = s
  (x, Laws.String.is_hex.era(x))

def Laws.String.is_hex.ok(x, str, val, h):
  %h : {Pair.fst(String, Bool, _) == x : String} & {Pair.snd(String, Bool, _) == Bool.not(String.is_empty(x)) && List.all(~&2, ~Char, ~(c => String.contains("0123456789abcdefABCDEF", SCon{c, SNil{}})), String.to_list(x)) : Bool}
  ({==}, {==})

def Laws.String.is_hex.era.ok(x, str, val, h):
  %h : {Pair.snd(String, Bool, _) == Laws.String.is_hex.era(x) : Bool}
  {==}

def Laws.String.is_unicode.era(x):
  +s = x
  List.all(~&2, ~Char, ~(c => (Char.to_u32(c) <= 1114111 : U32)), String.to_list(s))

def Laws.String.is_unicode(x):
  +s = x
  (s, Laws.String.is_unicode.era(s))

def Laws.String.is_unicode.ok(s, str, val, h):
  %h : {Pair.fst(String, Bool, _) == s : String} & {Pair.snd(String, Bool, _) == List.all(~&2, ~Char, ~(c => (Char.to_u32(c) <= 1114111 : U32)), String.to_list(s)) : Bool}
  ({==}, {==})

def Laws.String.is_unicode.era.ok(s, str, val, h):
  %h : {Pair.snd(String, Bool, _) == Laws.String.is_unicode.era(s) : Bool}
  {==}

def Laws.String.to_hex.era(x, h):
  match x:
    case SNil{}:
      0
    case SCon{c, t}:
      hex.go(t, dval(SCon{c, SNil{}}))

def Laws.String.to_hex(s, h):
  +x = s
  (x, Laws.String.to_hex.era(x, h))

def Laws.String.to_hex.borrows(x, h, str, val, e):
  %e : {Pair.fst(String, U32, _) == x : String}
  {==}

def Laws.String.to_hex.era.ok(x, h, str, val, e):
  %e : {Pair.snd(String, U32, _) == Laws.String.to_hex.era(x, h) : U32}
  {==}

# Rewriting a hypothesis about a Nat.
law tr:
  for -Q: Nat -> Type
  for -a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  for v: Q(a)
  Q(b)

def tr(Q, a, b, e, v):
  %e : Q(_)
  v

def ne(G: Type, s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{c, t}:
      G

# An empty string is no one-character string.
law ne.absurd:
  for -G: Type
  for -s0: Char
  for h: {SNil{} == SCon{s0, SNil{}} : String}
  G

def ne.absurd(G, s0, h):
  %h : ne(G, _)
  Unit{}

law zsplit.go:
  for -p: Nat
  for -t: Word(p)
  for s: {t == Word.zero(p) : Word(p)} | (&q:Nat -> {Word.to_nat(p, t) == 1n+q : Nat})
  {WCon{False{}, t} == Word.zero(1n+p) : Word(1n+p)} | (&q:Nat -> {Nat.double(Word.to_nat(p, t)) == 1n+q : Nat})

def zsplit.go(p, t, s):
  match s:
    case Inl{z}:
      Inl{Equal.cong(Word(p), Word(1n+p), u => WCon{False{}, u}, t, Word.zero(p), z)}
    case Inr{q}:
      match q:
        case (k, e):
          Inr{(1n+Nat.double(k), Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, t), 1n+k, e))}

# A word is all zeros, or its value is at least one.
law zsplit:
  for n: Nat
  for w: Word(n)
  {w == Word.zero(n) : Word(n)} | (&p:Nat -> {Word.to_nat(n, w) == 1n+p : Nat})

def zsplit(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Inl{{==}}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              Inr{(Nat.double(Word.to_nat(p, t)), {==})}
            case False{}:
              zsplit.go(p, t, zsplit(p, t))

law leaf.b0000.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b0000.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(Nat.double(Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0000:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b0000(r, s0, hs):
  leaf.b0000.go(r, s0, hs, zsplit(28n, r))

law leaf.b0001.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b0001.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(Nat.double(Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0001:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b0001(r, s0, hs):
  leaf.b0001.go(r, s0, hs, zsplit(28n, r))

law leaf.b0010.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b0010.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(Nat.double(1n+Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0010:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b0010(r, s0, hs):
  leaf.b0010.go(r, s0, hs, zsplit(28n, r))

law leaf.b0011.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b0011.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0011:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b0011(r, s0, hs):
  leaf.b0011.go(r, s0, hs, zsplit(28n, r))

law leaf.b0100.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b0100.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(1n+Nat.double(Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0100:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b0100(r, s0, hs):
  leaf.b0100.go(r, s0, hs, zsplit(28n, r))

law leaf.b0101.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b0101.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(1n+Nat.double(Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0101:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b0101(r, s0, hs):
  leaf.b0101.go(r, s0, hs, zsplit(28n, r))

law leaf.b0110.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b0110.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(1n+Nat.double(1n+Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0110:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b0110(r, s0, hs):
  leaf.b0110.go(r, s0, hs, zsplit(28n, r))

law leaf.b0111.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b0111.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", Nat.double(1n+Nat.double(1n+Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b0111:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b0111(r, s0, hs):
  leaf.b0111.go(r, s0, hs, zsplit(28n, r))

law leaf.b1000.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b1000.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(Nat.double(Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1000:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b1000(r, s0, hs):
  leaf.b1000.go(r, s0, hs, zsplit(28n, r))

law leaf.b1001.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b1001.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(Nat.double(Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1001:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b1001(r, s0, hs):
  leaf.b1001.go(r, s0, hs, zsplit(28n, r))

law leaf.b1010.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b1010.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(Nat.double(1n+Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1010:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b1010(r, s0, hs):
  leaf.b1010.go(r, s0, hs, zsplit(28n, r))

law leaf.b1011.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b1011.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(Nat.double(1n+Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1011:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b1011(r, s0, hs):
  leaf.b1011.go(r, s0, hs, zsplit(28n, r))

law leaf.b1100.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b1100.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(1n+Nat.double(Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1100:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, r}}}}} : U32}

def leaf.b1100(r, s0, hs):
  leaf.b1100.go(r, s0, hs, zsplit(28n, r))

law leaf.b1101.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b1101.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(1n+Nat.double(Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1101:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, r}}}}} : U32}

def leaf.b1101(r, s0, hs):
  leaf.b1101.go(r, s0, hs, zsplit(28n, r))

law leaf.b1110.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b1110.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(1n+Nat.double(1n+Nat.double(Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1110:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, r}}}}} : U32}

def leaf.b1110(r, s0, hs):
  leaf.b1110.go(r, s0, hs, zsplit(28n, r))

law leaf.b1111.go:
  for -r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  for s: {r == Word.zero(28n) : Word(28n)} | (&p:Nat -> {Word.to_nat(28n, r) == 1n+p : Nat})
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b1111.go(r, s0, hs, s):
  match s:
    case Inl{z}:
      %Equal.sym(Word(28n), r, Word.zero(28n), z) : {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, _}}}}} : U32}
      {==}
    case Inr{q}:
      match q:
        case (p, ep):
          ne.absurd({hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}, s0, tr(k => {String.take(String.drop("0123456789abcdef", 1n+Nat.double(1n+Nat.double(1n+Nat.double(1n+Nat.double(k))))), 1n) == SCon{s0, SNil{}} : String}, Word.to_nat(28n, r), 1n+p, ep, hs))

law leaf.b1111:
  for r: Word(28n)
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", Word.to_nat(32n, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}})), 1n)) == U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, r}}}}} : U32}

def leaf.b1111(r, s0, hs):
  leaf.b1111.go(r, s0, hs, zsplit(28n, r))

# A one-character string at position to_nat(n) of the digits has value n.
law key:
  for n: U32
  for -s0: Char
  for hs: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == SCon{s0, SNil{}} : String}
  {hv(String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n)) == n : U32}

def key(n, s0, hs):
  match n:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match b0:
            case False{}:
              match w1:
                case WCon{b1, w2}:
                  match b1:
                    case False{}:
                      match w2:
                        case WCon{b2, w3}:
                          match b2:
                            case False{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b0000(r, s0, hs)
                                    case True{}:
                                      leaf.b0001(r, s0, hs)
                            case True{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b0010(r, s0, hs)
                                    case True{}:
                                      leaf.b0011(r, s0, hs)
                    case True{}:
                      match w2:
                        case WCon{b2, w3}:
                          match b2:
                            case False{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b0100(r, s0, hs)
                                    case True{}:
                                      leaf.b0101(r, s0, hs)
                            case True{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b0110(r, s0, hs)
                                    case True{}:
                                      leaf.b0111(r, s0, hs)
            case True{}:
              match w1:
                case WCon{b1, w2}:
                  match b1:
                    case False{}:
                      match w2:
                        case WCon{b2, w3}:
                          match b2:
                            case False{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b1000(r, s0, hs)
                                    case True{}:
                                      leaf.b1001(r, s0, hs)
                            case True{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b1010(r, s0, hs)
                                    case True{}:
                                      leaf.b1011(r, s0, hs)
                    case True{}:
                      match w2:
                        case WCon{b2, w3}:
                          match b2:
                            case False{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b1100(r, s0, hs)
                                    case True{}:
                                      leaf.b1101(r, s0, hs)
                            case True{}:
                              match w3:
                                case WCon{b3, r}:
                                  match b3:
                                    case False{}:
                                      leaf.b1110(r, s0, hs)
                                    case True{}:
                                      leaf.b1111(r, s0, hs)

law dval.ok:
  for c: Char
  for n: U32
  for +hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(SCon{c, SNil{}}) : String}
  {dval(SCon{c, SNil{}}) == n : U32}

def dval.ok(c, n, hn):
  %hn : {hv(_) == n : U32}
  key(n, Char.to_lower(c), hn)

def is0(G: Type, k: Nat) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      G

def ge2.go(G: Type, p: Nat) -> Type:
  match p:
    case 0n:
      G
    case 1n+q:
      Unit

def ge2(G: Type, k: Nat) -> Type:
  match k:
    case 0n:
      G
    case 1n+p:
      ge2.go(G, p)

def isf(G: Type, b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# A one-character digit string has the value it is worth.
law one.go:
  for d: String
  for n: U32
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for -h: {Laws.String.is_hex.era(d) == True{} : Bool}
  {Laws.String.to_hex.era(d, h) == n : U32}

def one.go(d, n, hd, hn, h):
  match d:
    case SNil{}:
      %hd : is0({Laws.String.to_hex.era(SNil{}, h) == n : U32}, _)
      Unit{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          dval.ok(c, n, hn)
        case SCon{c2, t2}:
          %hd : ge2({Laws.String.to_hex.era(SCon{c, SCon{c2, t2}}, h) == n : U32}, _)
          Unit{}

def Laws.String.to_hex.one(d, n, hd, hn, h, str, val, e):
  %e : {Pair.snd(String, U32, _) == n : U32}
  one.go(d, n, hd, hn, h)

# Appending one digit to the digits read so far.
law go.snoc:
  for t: String
  for acc: U32
  for -c: Char
  {hex.go(t ++ SCon{c, SNil{}}, acc) == (hex.go(t, acc) * 16 + dval(SCon{c, SNil{}}) : U32) : U32}

def go.snoc(t, acc, c):
  match t:
    case SNil{}:
      {==}
    case SCon{h1, t1}:
      go.snoc(t1, (acc * 16 + dval(SCon{h1, SNil{}}) : U32), c)

# A nonempty digit string followed by one more digit.
law snoc.x:
  for x: String
  for -c: Char
  for hx: {Laws.String.is_hex.era(x) == True{} : Bool}
  for -h: {Laws.String.is_hex.era(x ++ SCon{c, SNil{}}) == True{} : Bool}
  {Laws.String.to_hex.era(x ++ SCon{c, SNil{}}, h) == (Laws.String.to_hex.era(x, hx) * 16 + dval(SCon{c, SNil{}}) : U32) : U32}

def snoc.x(x, c, hx, h):
  match x:
    case SNil{}:
      %hx : isf({Laws.String.to_hex.era(SNil{} ++ SCon{c, SNil{}}, h) == (Laws.String.to_hex.era(SNil{}, hx) * 16 + dval(SCon{c, SNil{}}) : U32) : U32}, _)
      Unit{}
    case SCon{h0, t0}:
      go.snoc(t0, dval(SCon{h0, SNil{}}), c)

# The appended string is one digit worth n.
law snoc.d:
  for x: String
  for d: String
  for n: U32
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for hx: {Laws.String.is_hex.era(x) == True{} : Bool}
  for -h: {Laws.String.is_hex.era(x ++ d) == True{} : Bool}
  {Laws.String.to_hex.era(x ++ d, h) == (Laws.String.to_hex.era(x, hx) * 16 + n : U32) : U32}

def snoc.d(x, d, n, hd, hn, hx, h):
  match d:
    case SNil{}:
      %hd : is0({Laws.String.to_hex.era(x ++ SNil{}, h) == (Laws.String.to_hex.era(x, hx) * 16 + n : U32) : U32}, _)
      Unit{}
    case SCon{c, t}:
      match t:
        case SCon{c2, t2}:
          %hd : ge2({Laws.String.to_hex.era(x ++ SCon{c, SCon{c2, t2}}, h) == (Laws.String.to_hex.era(x, hx) * 16 + n : U32) : U32}, _)
          Unit{}
        case SNil{}:
          %dval.ok(c, n, hn) : {Laws.String.to_hex.era(x ++ SCon{c, SNil{}}, h) == (Laws.String.to_hex.era(x, hx) * 16 + _ : U32) : U32}
          snoc.x(x, c, hx, h)

def Laws.String.to_hex.snoc(x, d, n, hd, hn, hx, xstr, xval, ex, h, str, val, e):
  %e : {Pair.snd(String, U32, _) == (xval * 16 + n : U32) : U32}
  %ex : {Laws.String.to_hex.era(x ++ d, h) == (Pair.snd(String, U32, _) * 16 + n : U32) : U32}
  snoc.d(x, d, n, hd, hn, hx, h)
