# Utilities that Base doesn't have yet.

import Base

# =========
# SPEC Sing
# =========

# Sing(~A, a): a copy of a. The predicate that keeps plain data when lifting.
law Sing:
  for ~A: Type
  for -a: A
  Type

law Sing.make:
  for ~A: Type
  for a: A
  Sing(~A, a)

law Sing.rec:
  for ~A: Type
  for ~Q: @-a:A -> Sing(~A, a) -> Type
  for ~f: @a:A -> Q(a, Sing.make(~A, a))
  for -a: A
  for s: Sing(~A, a)
  Q(a, s)

law Sing.rec.make:
  for ~A: Type
  for ~Q: @-a:A -> Sing(~A, a) -> Type
  for ~f: @a:A -> Q(a, Sing.make(~A, a))
  for a: A
  {Sing.rec(~A, ~Q, ~f, a, Sing.make(~A, a)) == f(a) : Q(a, Sing.make(~A, a))}

# =============
# SPEC Pair.All
# =============

# Pair.All(~A, ~B, ~PA, ~PB, p): PA holds of the first component of p, and PB of the second.
law Pair.All:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for -p: A & B
  Type

law Pair.All.make:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for -a: A
  for -b: B
  for pa: PA(a)
  for pb: PB(b)
  Pair.All(~A, ~B, ~PA, ~PB, (a, b))

law Pair.All.rec:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for ~Q: @-p:A & B -> Pair.All(~A, ~B, ~PA, ~PB, p) -> Type
  for ~f: @-a:A -> @-b:B -> @pa:PA(a) -> @pb:PB(b) -> Q((a, b), Pair.All.make(~A, ~B, ~PA, ~PB, a, b, pa, pb))
  for -p: A & B
  for x: Pair.All(~A, ~B, ~PA, ~PB, p)
  Q(p, x)

law Pair.All.rec.make:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for ~Q: @-p:A & B -> Pair.All(~A, ~B, ~PA, ~PB, p) -> Type
  for ~f: @-a:A -> @-b:B -> @pa:PA(a) -> @pb:PB(b) -> Q((a, b), Pair.All.make(~A, ~B, ~PA, ~PB, a, b, pa, pb))
  for -a: A
  for -b: B
  for pa: PA(a)
  for pb: PB(b)
  {Pair.All.rec(~A, ~B, ~PA, ~PB, ~Q, ~f, (a, b), Pair.All.make(~A, ~B, ~PA, ~PB, a, b, pa, pb)) == f(a, b, pa, pb) : Q((a, b), Pair.All.make(~A, ~B, ~PA, ~PB, a, b, pa, pb))}

# Pair.All.of(~fa, ~fb, p): the Pair.All whose proofs for (a, b) are fa(a) and fb(b).
law Pair.All.of:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for ~fa: @a:A -> PA(a)
  for ~fb: @b:B -> PB(b)
  for p: A & B
  Pair.All(~A, ~B, ~PA, ~PB, p)

law Pair.All.of.make:
  for ~A: Type
  for ~B: Type
  for ~PA: @-x:A -> Type
  for ~PB: @-x:B -> Type
  for ~fa: @a:A -> PA(a)
  for ~fb: @b:B -> PB(b)
  for a: A
  for b: B
  {Pair.All.of(~A, ~B, ~PA, ~PB, ~fa, ~fb, (a, b)) == Pair.All.make(~A, ~B, ~PA, ~PB, a, b, fa(a), fb(b)) : Pair.All(~A, ~B, ~PA, ~PB, (a, b))}

# =============
# SPEC List.All
# =============

# List.All(~A, ~P, xs): P holds of every element of xs.
law List.All:
  for ~A: Type
  for ~P: @-x:A -> Type
  for -xs: List<A>
  Type

law List.All.nil:
  for ~A: Type
  for ~P: @-x:A -> Type
  List.All(~A, ~P, [])

law List.All.cons:
  for ~A: Type
  for ~P: @-x:A -> Type
  for -x: A
  for -xs: List<A>
  for px: P(x)
  for rest: List.All(~A, ~P, xs)
  List.All(~A, ~P, x <> xs)

law List.All.rec:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @-rest:List.All(~A, ~P, xs) -> Q(xs, rest) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  for -xs: List<A>
  for a: List.All(~A, ~P, xs)
  Q(xs, a)

law List.All.rec.nil:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @-rest:List.All(~A, ~P, xs) -> Q(xs, rest) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  {List.All.rec(~A, ~P, ~Q, ~on_nil, ~on_cons, [], List.All.nil(~A, ~P)) == on_nil : Q([], List.All.nil(~A, ~P))}

law List.All.rec.cons:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @-rest:List.All(~A, ~P, xs) -> Q(xs, rest) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  for -x: A
  for -xs: List<A>
  for px: P(x)
  for rest: List.All(~A, ~P, xs)
  {List.All.rec(~A, ~P, ~Q, ~on_nil, ~on_cons, x <> xs, List.All.cons(~A, ~P, x, xs, px, rest)) == on_cons(x, xs, px, rest, List.All.rec(~A, ~P, ~Q, ~on_nil, ~on_cons, xs, rest)) : Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))}

# Case analysis: like rec, but each case gets its fields live and no results.
law List.All.cases:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @rest:List.All(~A, ~P, xs) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  for -xs: List<A>
  for a: List.All(~A, ~P, xs)
  Q(xs, a)

law List.All.cases.nil:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @rest:List.All(~A, ~P, xs) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  {List.All.cases(~A, ~P, ~Q, ~on_nil, ~on_cons, [], List.All.nil(~A, ~P)) == on_nil : Q([], List.All.nil(~A, ~P))}

law List.All.cases.cons:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~Q: @-xs:List<A> -> List.All(~A, ~P, xs) -> Type
  for ~on_nil: Q([], List.All.nil(~A, ~P))
  for ~on_cons: @-x:A -> @-xs:List<A> -> @px:P(x) -> @rest:List.All(~A, ~P, xs) -> Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))
  for -x: A
  for -xs: List<A>
  for px: P(x)
  for rest: List.All(~A, ~P, xs)
  {List.All.cases(~A, ~P, ~Q, ~on_nil, ~on_cons, x <> xs, List.All.cons(~A, ~P, x, xs, px, rest)) == on_cons(x, xs, px, rest) : Q(x <> xs, List.All.cons(~A, ~P, x, xs, px, rest))}

# List.All.of(~f, xs): the List.All whose proof for each element x is f(x).
law List.All.of:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~f: @x:A -> P(x)
  for xs: List<A>
  List.All(~A, ~P, xs)

law List.All.of.nil:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~f: @x:A -> P(x)
  {List.All.of(~A, ~P, ~f, []) == List.All.nil(~A, ~P) : List.All(~A, ~P, [])}

law List.All.of.cons:
  for ~A: Type
  for ~P: @-x:A -> Type
  for ~f: @x:A -> P(x)
  for x: A
  for xs: List<A>
  {List.All.of(~A, ~P, ~f, x <> xs) == List.All.cons(~A, ~P, x, xs, f(x), List.All.of(~A, ~P, ~f, xs)) : List.All(~A, ~P, x <> xs)}

# ===========
# SPEC String
# ===========

# is_hex(x) hands x back beside whether x is one or more hexadecimal digits.
law String.is_hex:
  for x: String
  String & Bool

law String.is_hex.ok:
  for x: String
  for -str: String
  for -val: Bool
  for h: {String.is_hex(x) == (str, val) : String & Bool}
  {str == x : String}
  & {val == Bool.not(String.is_empty(x)) && List.all(~&2, ~Char, ~(c => String.contains("0123456789abcdefABCDEF", SCon{c, SNil{}})), String.to_list(x)) : Bool}

law String.is_hex.era:
  for x: String
  Bool

law String.is_hex.era.ok:
  for x: String
  for -str: String
  for -val: Bool
  for h: {String.is_hex(x) == (str, val) : String & Bool}
  {val == String.is_hex.era(x) : Bool}

# is_unicode(s) hands s back beside whether every character of s is a Unicode code point, at most U+10FFFF.
law String.is_unicode:
  for s: String
  String & Bool

law String.is_unicode.ok:
  for s: String
  for -str: String
  for -val: Bool
  for h: {String.is_unicode(s) == (str, val) : String & Bool}
  {str == s : String}
  & {val == List.all(~&2, ~Char, ~(c => (Char.to_u32(c) <= 1114111 : U32)), String.to_list(s)) : Bool}

law String.is_unicode.era:
  for s: String
  Bool

law String.is_unicode.era.ok:
  for s: String
  for -str: String
  for -val: Bool
  for h: {String.is_unicode(s) == (str, val) : String & Bool}
  {val == String.is_unicode.era(s) : Bool}

# to_hex(x, h) hands x back beside the value of the hexadecimal digits x, modulo 2^32.
law String.to_hex:
  for x: String
  for h: {String.is_hex.era(x) == True{} : Bool}
  String & U32

law String.to_hex.borrows:
  for x: String
  for h: {String.is_hex.era(x) == True{} : Bool}
  for -str: String
  for -val: U32
  for e: {String.to_hex(x, h) == (str, val) : String & U32}
  {str == x : String}

# One digit d is worth n.
law String.to_hex.one:
  for d: String
  for n: U32
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for h: {String.is_hex.era(d) == True{} : Bool}
  for -str: String
  for -val: U32
  for e: {String.to_hex(d, h) == (str, val) : String & U32}
  {val == n : U32}

# Appending a digit d worth n multiplies the value so far by 16 and adds n.
law String.to_hex.snoc:
  for x: String
  for d: String
  for n: U32
  for hd: {String.length(d) == 1n : Nat}
  for hn: {String.take(String.drop("0123456789abcdef", U32.to_nat(n)), 1n) == String.to_lower(d) : String}
  for hx: {String.is_hex.era(x) == True{} : Bool}
  for -xstr: String
  for -xval: U32
  for ex: {String.to_hex(x, hx) == (xstr, xval) : String & U32}
  for h: {String.is_hex.era(x ++ d) == True{} : Bool}
  for -str: String
  for -val: U32
  for e: {String.to_hex(x ++ d, h) == (str, val) : String & U32}
  {val == (xval * 16 + n : U32) : U32}

law String.to_hex.era:
  for x: String
  for h: {String.is_hex.era(x) == True{} : Bool}
  U32

law String.to_hex.era.ok:
  for x: String
  for h: {String.is_hex.era(x) == True{} : Bool}
  for -str: String
  for -val: U32
  for e: {String.to_hex(x, h) == (str, val) : String & U32}
  {val == String.to_hex.era(x, h) : U32}
