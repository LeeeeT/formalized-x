# JSON, as specified by RFC 8259.
#
# A number is kept as the text it was written with, so no precision is lost.
# An object's members are kept in order, duplicate names included.
# Where the RFC is silent: an unpaired surrogate escape such as "\uD800" stands
# for that code point by itself (RFC 8259, section 8.2).

import Base
import ../abnf/LAWS.bend as ABNF
import ../base-extra/LAWS.bend as Extra

# ============
# SPEC grammar
# ============

law grammar:
  List<(String & ABNF.Rule)>

law grammar.ok:
  for name: String
  for s: String
  {ABNF.matches.era(grammar, name, s) == ABNF.matches.era([
    ("JSON-text", ABNF.seq([ABNF.ref("ws"), ABNF.ref("value"), ABNF.ref("ws")])),
    ("begin-array", ABNF.seq([ABNF.ref("ws"), ABNF.char('['), ABNF.ref("ws")])),
    ("begin-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('{'), ABNF.ref("ws")])),
    ("end-array", ABNF.seq([ABNF.ref("ws"), ABNF.char(']'), ABNF.ref("ws")])),
    ("end-object", ABNF.seq([ABNF.ref("ws"), ABNF.char('}'), ABNF.ref("ws")])),
    ("name-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(':'), ABNF.ref("ws")])),
    ("value-separator", ABNF.seq([ABNF.ref("ws"), ABNF.char(','), ABNF.ref("ws")])),
    ("ws", ABNF.rep.any(ABNF.alt([ABNF.char(Chr{32}), ABNF.char(Chr{9}), ABNF.char(Chr{10}), ABNF.char(Chr{13})]))),
    ("value", ABNF.alt([ABNF.ref("false"), ABNF.ref("null"), ABNF.ref("true"), ABNF.ref("object"), ABNF.ref("array"), ABNF.ref("number"), ABNF.ref("string")])),
    ("false", ABNF.string.case_sensitive("false")),
    ("null", ABNF.string.case_sensitive("null")),
    ("true", ABNF.string.case_sensitive("true")),
    ("object", ABNF.seq([ABNF.ref("begin-object"), ABNF.opt(ABNF.seq([ABNF.ref("member"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("member")]))])), ABNF.ref("end-object")])),
    ("member", ABNF.seq([ABNF.ref("string"), ABNF.ref("name-separator"), ABNF.ref("value")])),
    ("array", ABNF.seq([ABNF.ref("begin-array"), ABNF.opt(ABNF.seq([ABNF.ref("value"), ABNF.rep.any(ABNF.seq([ABNF.ref("value-separator"), ABNF.ref("value")]))])), ABNF.ref("end-array")])),
    ("number", ABNF.seq([ABNF.opt(ABNF.ref("minus")), ABNF.ref("int"), ABNF.opt(ABNF.ref("frac")), ABNF.opt(ABNF.ref("exp"))])),
    ("decimal-point", ABNF.char('.')),
    ("digit1-9", ABNF.range('1', '9')),
    ("e", ABNF.alt([ABNF.char('e'), ABNF.char('E')])),
    ("exp", ABNF.seq([ABNF.ref("e"), ABNF.opt(ABNF.alt([ABNF.ref("minus"), ABNF.ref("plus")])), ABNF.rep.at_least(1n, ABNF.core.digit)])),
    ("frac", ABNF.seq([ABNF.ref("decimal-point"), ABNF.rep.at_least(1n, ABNF.core.digit)])),
    ("int", ABNF.alt([ABNF.ref("zero"), ABNF.seq([ABNF.ref("digit1-9"), ABNF.rep.any(ABNF.core.digit)])])),
    ("minus", ABNF.char('-')),
    ("plus", ABNF.char('+')),
    ("zero", ABNF.char('0')),
    ("string", ABNF.seq([ABNF.ref("quotation-mark"), ABNF.rep.any(ABNF.ref("char")), ABNF.ref("quotation-mark")])),
    ("char", ABNF.alt([ABNF.ref("unescaped"), ABNF.seq([ABNF.ref("escape"), ABNF.alt([ABNF.char('"'), ABNF.char('\\'), ABNF.char('/'), ABNF.char('b'), ABNF.char('f'), ABNF.char('n'), ABNF.char('r'), ABNF.char('t'), ABNF.seq([ABNF.char('u'), ABNF.rep.exactly(4n, ABNF.core.hexdig)])])])])),
    ("escape", ABNF.char('\\')),
    ("quotation-mark", ABNF.char('"')),
    ("unescaped", ABNF.alt([ABNF.range(Chr{32}, Chr{33}), ABNF.range(Chr{35}, Chr{91}), ABNF.range(Chr{93}, Chr{1114111})]))
  ], name, s) : Bool}

# ===========
# SPEC decode
# ===========

# decode(x) hands x back beside the characters that x, the inside of a JSON
# string, stands for. decode.era(x) gives the same characters without handing x
# back.
law decode:
  for x: String
  String & String

law decode.borrows:
  for x: String
  for -str: String
  for -val: String
  for h: {decode(x) == (str, val) : String & String}
  {str == x : String}

law decode.era:
  for x: String
  String

law decode.era.ok:
  for x: String
  for -str: String
  for -val: String
  for h: {decode(x) == (str, val) : String & String}
  {val == decode.era(x) : String}

law decode.nil:
  {decode.era("") == "" : String}

# char = unescaped
law decode.unescaped:
  for u: String
  for t: String
  for h: {ABNF.matches.era(grammar, "unescaped", u) == True{} : Bool}
  {decode.era(u ++ t) == u ++ decode.era(t) : String}

# char = escape (%x22 / %x5C / %x2F / %x62 / %x66 / %x6E / %x72 / %x74 / ...)
law decode.escape:
  for e: String
  for t: String
  for he: {ABNF.matches.era(grammar, "escape", e) == True{} : Bool}
  {decode.era(e ++ "\"" ++ t) == "\"" ++ decode.era(t) : String}
  & {decode.era(e ++ "\\" ++ t) == "\\" ++ decode.era(t) : String}
  & {decode.era(e ++ "/" ++ t) == "/" ++ decode.era(t) : String}
  & {decode.era(e ++ "b" ++ t) == SCon{Chr{8}, decode.era(t)} : String}
  & {decode.era(e ++ "f" ++ t) == SCon{Chr{12}, decode.era(t)} : String}
  & {decode.era(e ++ "n" ++ t) == SCon{Chr{10}, decode.era(t)} : String}
  & {decode.era(e ++ "r" ++ t) == SCon{Chr{13}, decode.era(t)} : String}
  & {decode.era(e ++ "t" ++ t) == SCon{Chr{9}, decode.era(t)} : String}

# char = escape %x75 4HEXDIG, where XXXX is not a high surrogate U+D800 to U+DBFF.
law decode.u:
  for e: String
  for x: String
  for t: String
  for he: {ABNF.matches.era(grammar, "escape", e) == True{} : Bool}
  for hx: {Extra.String.is_hex.era(x) == True{} : Bool}
  for lx: {String.length(x) == 4n : Nat}
  for hs: {((Extra.String.to_hex.era(x, hx) < 55296 : U32) || (Extra.String.to_hex.era(x, hx) > 56319 : U32)) == True{} : Bool}
  {decode.era(e ++ "u" ++ x ++ t) == SCon{Chr{Extra.String.to_hex.era(x, hx)}, decode.era(t)} : String}

# A surrogate pair \uD800-\uDBFF \uDC00-\uDFFF stands for one character above U+FFFF.
law decode.pair:
  for e: String
  for x1: String
  for x2: String
  for t: String
  for he: {ABNF.matches.era(grammar, "escape", e) == True{} : Bool}
  for hx1: {Extra.String.is_hex.era(x1) == True{} : Bool}
  for lx1: {String.length(x1) == 4n : Nat}
  for hx2: {Extra.String.is_hex.era(x2) == True{} : Bool}
  for lx2: {String.length(x2) == 4n : Nat}
  for hs1: {((Extra.String.to_hex.era(x1, hx1) >= 55296 : U32) && (Extra.String.to_hex.era(x1, hx1) <= 56319 : U32)) == True{} : Bool}
  for hs2: {((Extra.String.to_hex.era(x2, hx2) >= 56320 : U32) && (Extra.String.to_hex.era(x2, hx2) <= 57343 : U32)) == True{} : Bool}
  {decode.era(e ++ "u" ++ x1 ++ e ++ "u" ++ x2 ++ t) == SCon{Chr{(65536 + (Extra.String.to_hex.era(x1, hx1) - 55296) * 1024 + (Extra.String.to_hex.era(x2, hx2) - 56320) : U32)}, decode.era(t)} : String}

# A high surrogate with no \u after it stands for itself.
law decode.high:
  for e: String
  for x: String
  for t: String
  for he: {ABNF.matches.era(grammar, "escape", e) == True{} : Bool}
  for hx: {Extra.String.is_hex.era(x) == True{} : Bool}
  for lx: {String.length(x) == 4n : Nat}
  for hs: {((Extra.String.to_hex.era(x, hx) >= 55296 : U32) && (Extra.String.to_hex.era(x, hx) <= 56319 : U32)) == True{} : Bool}
  for ht: {String.starts_with(t, e ++ "u") == False{} : Bool}
  {decode.era(e ++ "u" ++ x ++ t) == SCon{Chr{Extra.String.to_hex.era(x, hx)}, decode.era(t)} : String}

# A high surrogate followed by a \u that isn't a low surrogate stands for itself.
law decode.high_u:
  for e: String
  for x1: String
  for x2: String
  for t: String
  for he: {ABNF.matches.era(grammar, "escape", e) == True{} : Bool}
  for hx1: {Extra.String.is_hex.era(x1) == True{} : Bool}
  for lx1: {String.length(x1) == 4n : Nat}
  for hx2: {Extra.String.is_hex.era(x2) == True{} : Bool}
  for lx2: {String.length(x2) == 4n : Nat}
  for hs1: {((Extra.String.to_hex.era(x1, hx1) >= 55296 : U32) && (Extra.String.to_hex.era(x1, hx1) <= 56319 : U32)) == True{} : Bool}
  for hs2: {((Extra.String.to_hex.era(x2, hx2) < 56320 : U32) || (Extra.String.to_hex.era(x2, hx2) > 57343 : U32)) == True{} : Bool}
  {decode.era(e ++ "u" ++ x1 ++ e ++ "u" ++ x2 ++ t) == SCon{Chr{Extra.String.to_hex.era(x1, hx1)}, decode.era(e ++ "u" ++ x2 ++ t)} : String}

# What decode gives for the inside of a JSON string is always Unicode.
law decode.unicode:
  for q1: String
  for x: String
  for q2: String
  for hq1: {ABNF.matches.era(grammar, "quotation-mark", q1) == True{} : Bool}
  for hq2: {ABNF.matches.era(grammar, "quotation-mark", q2) == True{} : Bool}
  for hx: {ABNF.matches.era(grammar, "string", q1 ++ x ++ q2) == True{} : Bool}
  {Extra.String.is_unicode.era(decode.era(x)) == True{} : Bool}

# ===========
# SPEC Number
# ===========

law Number:
  Type

# Number.make(n, h): the number written as n.
law Number.make:
  for n: String
  for h: {ABNF.matches.era(grammar, "number", n) == True{} : Bool}
  Number

law Number.rec:
  for ~P: @-x:Number -> Type
  for ~f: @n:String -> @h:{ABNF.matches.era(grammar, "number", n) == True{} : Bool} -> P(Number.make(n, h))
  for x: Number
  P(x)

law Number.rec.make:
  for ~P: @-x:Number -> Type
  for ~f: @n:String -> @h:{ABNF.matches.era(grammar, "number", n) == True{} : Bool} -> P(Number.make(n, h))
  for n: String
  for h: {ABNF.matches.era(grammar, "number", n) == True{} : Bool}
  {Number.rec(~P, ~f, Number.make(n, h)) == f(n, h) : P(Number.make(n, h))}

# Number.make.try(n) gives Inr with the number n when n is one, and hands n back
# in Inl when it isn't.
law Number.make.try:
  for n: String
  String | Number

law Number.make.try.valid:
  for n: String
  for h: {ABNF.matches.era(grammar, "number", n) == True{} : Bool}
  {Number.make.try(n) == Inr{Number.make(n, h)} : String | Number}

law Number.make.try.invalid:
  for n: String
  for h: {ABNF.matches.era(grammar, "number", n) == False{} : Bool}
  {Number.make.try(n) == Inl{n} : String | Number}

# Number.make.try.era(n) gives what Number.make.try(n) gives, as a Maybe:
# Some when n is a number, and None, dropping n, when it isn't.
law Number.make.try.era:
  for n: String
  Maybe<Number>

law Number.make.try.era.valid:
  for n: String
  for -y: Number
  for h: {Number.make.try(n) == Inr{y} : String | Number}
  {Number.make.try.era(n) == Some{y} : Maybe<Number>}

law Number.make.try.era.invalid:
  for n: String
  for -str: String
  for h: {Number.make.try(n) == Inl{str} : String | Number}
  {Number.make.try.era(n) == None{} : Maybe<Number>}

# =========
# SPEC Text
# =========

law Text:
  Type

# Text.make(s, h): the string s, whose characters are all Unicode code points,
# so a JSON string can write it.
law Text.make:
  for s: String
  for h: {Extra.String.is_unicode.era(s) == True{} : Bool}
  Text

law Text.rec:
  for ~P: @-x:Text -> Type
  for ~f: @s:String -> @h:{Extra.String.is_unicode.era(s) == True{} : Bool} -> P(Text.make(s, h))
  for x: Text
  P(x)

law Text.rec.make:
  for ~P: @-x:Text -> Type
  for ~f: @s:String -> @h:{Extra.String.is_unicode.era(s) == True{} : Bool} -> P(Text.make(s, h))
  for s: String
  for h: {Extra.String.is_unicode.era(s) == True{} : Bool}
  {Text.rec(~P, ~f, Text.make(s, h)) == f(s, h) : P(Text.make(s, h))}

# Text.make.try(s) gives Inr with the text s when s is one, and hands s back
# in Inl when it isn't.
law Text.make.try:
  for s: String
  String | Text

law Text.make.try.valid:
  for s: String
  for h: {Extra.String.is_unicode.era(s) == True{} : Bool}
  {Text.make.try(s) == Inr{Text.make(s, h)} : String | Text}

law Text.make.try.invalid:
  for s: String
  for h: {Extra.String.is_unicode.era(s) == False{} : Bool}
  {Text.make.try(s) == Inl{s} : String | Text}

# Text.make.try.era(s) gives what Text.make.try(s) gives, as a Maybe:
# Some when s is Unicode, and None, dropping s, when it isn't.
law Text.make.try.era:
  for s: String
  Maybe<Text>

law Text.make.try.era.valid:
  for s: String
  for -y: Text
  for h: {Text.make.try(s) == Inr{y} : String | Text}
  {Text.make.try.era(s) == Some{y} : Maybe<Text>}

law Text.make.try.era.invalid:
  for s: String
  for -str: String
  for h: {Text.make.try(s) == Inl{str} : String | Text}
  {Text.make.try.era(s) == None{} : Maybe<Text>}

# ==========
# SPEC Value
# ==========

law Value:
  Type

law Value.null:
  Value

law Value.bool:
  for b: Bool
  Value

law Value.number:
  for n: Number
  Value

law Value.string:
  for t: Text
  Value

law Value.array:
  for a: List<Value>
  Value

law Value.object:
  for o: List<(Text & Value)>
  Value

law Value.rec:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for v: Value
  P(v)

law Value.rec.null:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.null) == on_null : P(Value.null)}

law Value.rec.bool:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for b: Bool
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.bool(b)) == on_bool(b) : P(Value.bool(b))}

law Value.rec.number:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for n: Number
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.number(n)) == on_number(n) : P(Value.number(n))}

law Value.rec.string:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for t: Text
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.string(t)) == on_string(t) : P(Value.string(t))}

# Each element's proof is rec of that element.
law Value.rec.array:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for a: List<Value>
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.array(a)) == on_array(a, Extra.List.All.of(~Value, ~P, ~Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object), a)) : P(Value.array(a))}

# Each member's proof is a copy of its key, beside rec of its value.
law Value.rec.object:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @-a:List<Value> -> Extra.List.All(~Value, ~P, a) -> P(Value.array(a))
  for ~on_object: @-o:List<(Text & Value)> -> Extra.List.All(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), o) -> P(Value.object(o))
  for o: List<(Text & Value)>
  {Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.object(o)) == on_object(o, Extra.List.All.of(~(Text & Value), ~Extra.Pair.All(~Text, ~Value, ~Extra.Sing(~Text), ~P), ~Extra.Pair.All.of(~Text, ~Value, ~Extra.Sing(~Text), ~P, ~Extra.Sing.make(~Text), ~Value.rec(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object)), o)) : P(Value.object(o))}

# Case analysis. Unlike rec, each case gets its fields live and no results for
# the values inside, so it can hand the value back.
law Value.cases:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for v: Value
  P(v)

law Value.cases.null:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.null) == on_null : P(Value.null)}

law Value.cases.bool:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for b: Bool
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.bool(b)) == on_bool(b) : P(Value.bool(b))}

law Value.cases.number:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for n: Number
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.number(n)) == on_number(n) : P(Value.number(n))}

law Value.cases.string:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for t: Text
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.string(t)) == on_string(t) : P(Value.string(t))}

law Value.cases.array:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for a: List<Value>
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.array(a)) == on_array(a) : P(Value.array(a))}

law Value.cases.object:
  for ~P: @-x:Value -> Type
  for ~on_null: P(Value.null)
  for ~on_bool: @b:Bool -> P(Value.bool(b))
  for ~on_number: @n:Number -> P(Value.number(n))
  for ~on_string: @t:Text -> P(Value.string(t))
  for ~on_array: @a:List<Value> -> P(Value.array(a))
  for ~on_object: @o:List<(Text & Value)> -> P(Value.object(o))
  for o: List<(Text & Value)>
  {Value.cases(~P, ~on_null, ~on_bool, ~on_number, ~on_string, ~on_array, ~on_object, Value.object(o)) == on_object(o) : P(Value.object(o))}

# Value.as_null(v) gives Inr with Unit{} and a setter when v is null, and hands
# v back in Inl when it isn't. Value.as_null.dup(v) hands v back beside whether
# it is null, and Value.as_null.era(v) gives that without v.
law Value.as_null:
  for v: Value
  Value | (Unit & (Unit -> Value))

law Value.as_null.ok:
  for v: Value
  {Value.as_null(v) == Value.cases(~(_ => Value | (Unit & (Unit -> Value))), ~Inr{(Unit{}, u => Value.null)}, ~(b => Inl{Value.bool(b)}), ~(n => Inl{Value.number(n)}), ~(t => Inl{Value.string(t)}), ~(a => Inl{Value.array(a)}), ~(o => Inl{Value.object(o)}), v) : Value | (Unit & (Unit -> Value))}

law Value.as_null.dup:
  for v: Value
  Value & Maybe<Unit>

law Value.as_null.dup.ok:
  for v: Value
  {Value.as_null.dup(v) == Value.cases(~(_ => Value & Maybe<Unit>), ~(Value.null, Some{Unit{}}), ~(b => (Value.bool(b), None{})), ~(n => (Value.number(n), None{})), ~(t => (Value.string(t), None{})), ~(a => (Value.array(a), None{})), ~(o => (Value.object(o), None{})), v) : Value & Maybe<Unit>}

law Value.as_null.era:
  for v: Value
  Maybe<Unit>

law Value.as_null.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<Unit>
  for h: {Value.as_null.dup(v) == (w, val) : Value & Maybe<Unit>}
  {val == Value.as_null.era(v) : Maybe<Unit>}

# Value.as_bool(v) gives Inr with its bool and a setter that puts a new one in
# its place when v is a bool, and hands v back in Inl when it isn't.
# Value.as_bool.dup(v) hands v back beside a copy of its bool, and
# Value.as_bool.era(v) gives the copy without v.
law Value.as_bool:
  for v: Value
  Value | (Bool & (Bool -> Value))

law Value.as_bool.ok:
  for v: Value
  {Value.as_bool(v) == Value.cases(~(_ => Value | (Bool & (Bool -> Value))), ~Inl{Value.null}, ~(b => Inr{(b, Value.bool)}), ~(n => Inl{Value.number(n)}), ~(t => Inl{Value.string(t)}), ~(a => Inl{Value.array(a)}), ~(o => Inl{Value.object(o)}), v) : Value | (Bool & (Bool -> Value))}

law Value.as_bool.dup:
  for v: Value
  Value & Maybe<Bool>

law Value.as_bool.dup.ok:
  for v: Value
  {Value.as_bool.dup(v) == Value.cases(~(_ => Value & Maybe<Bool>), ~(Value.null, None{}), ~(b => (Value.bool(b), Some{b})), ~(n => (Value.number(n), None{})), ~(t => (Value.string(t), None{})), ~(a => (Value.array(a), None{})), ~(o => (Value.object(o), None{})), v) : Value & Maybe<Bool>}

law Value.as_bool.era:
  for v: Value
  Maybe<Bool>

law Value.as_bool.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<Bool>
  for h: {Value.as_bool.dup(v) == (w, val) : Value & Maybe<Bool>}
  {val == Value.as_bool.era(v) : Maybe<Bool>}

# Value.as_number(v) gives Inr with its number and a setter that puts a new one
# in its place when v is a number, and hands v back in Inl when it isn't.
# Value.as_number.dup(v) hands v back beside a copy of its number, and
# Value.as_number.era(v) gives the copy without v.
law Value.as_number:
  for v: Value
  Value | (Number & (Number -> Value))

law Value.as_number.ok:
  for v: Value
  {Value.as_number(v) == Value.cases(~(_ => Value | (Number & (Number -> Value))), ~Inl{Value.null}, ~(b => Inl{Value.bool(b)}), ~(n => Inr{(n, Value.number)}), ~(t => Inl{Value.string(t)}), ~(a => Inl{Value.array(a)}), ~(o => Inl{Value.object(o)}), v) : Value | (Number & (Number -> Value))}

law Value.as_number.dup:
  for v: Value
  Value & Maybe<Number>

law Value.as_number.dup.ok:
  for v: Value
  {Value.as_number.dup(v) == Value.cases(~(_ => Value & Maybe<Number>), ~(Value.null, None{}), ~(b => (Value.bool(b), None{})), ~(n => (Value.number(n), Some{n})), ~(t => (Value.string(t), None{})), ~(a => (Value.array(a), None{})), ~(o => (Value.object(o), None{})), v) : Value & Maybe<Number>}

law Value.as_number.era:
  for v: Value
  Maybe<Number>

law Value.as_number.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<Number>
  for h: {Value.as_number.dup(v) == (w, val) : Value & Maybe<Number>}
  {val == Value.as_number.era(v) : Maybe<Number>}

# Value.as_string(v) gives Inr with its text and a setter that puts a new one in
# its place when v is a string, and hands v back in Inl when it isn't.
# Value.as_string.dup(v) hands v back beside a copy of its text, and
# Value.as_string.era(v) gives the copy without v.
law Value.as_string:
  for v: Value
  Value | (Text & (Text -> Value))

law Value.as_string.ok:
  for v: Value
  {Value.as_string(v) == Value.cases(~(_ => Value | (Text & (Text -> Value))), ~Inl{Value.null}, ~(b => Inl{Value.bool(b)}), ~(n => Inl{Value.number(n)}), ~(t => Inr{(t, Value.string)}), ~(a => Inl{Value.array(a)}), ~(o => Inl{Value.object(o)}), v) : Value | (Text & (Text -> Value))}

law Value.as_string.dup:
  for v: Value
  Value & Maybe<Text>

law Value.as_string.dup.ok:
  for v: Value
  {Value.as_string.dup(v) == Value.cases(~(_ => Value & Maybe<Text>), ~(Value.null, None{}), ~(b => (Value.bool(b), None{})), ~(n => (Value.number(n), None{})), ~(t => (Value.string(t), Some{t})), ~(a => (Value.array(a), None{})), ~(o => (Value.object(o), None{})), v) : Value & Maybe<Text>}

law Value.as_string.era:
  for v: Value
  Maybe<Text>

law Value.as_string.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<Text>
  for h: {Value.as_string.dup(v) == (w, val) : Value & Maybe<Text>}
  {val == Value.as_string.era(v) : Maybe<Text>}

# Value.as_array(v) gives Inr with its elements and a setter that puts new ones
# in their place when v is an array, and hands v back in Inl when it isn't.
# Value.as_array.dup(v) hands v back beside a copy of its elements, and
# Value.as_array.era(v) gives the copy without v.
law Value.as_array:
  for v: Value
  Value | (List<Value> & (List<Value> -> Value))

law Value.as_array.ok:
  for v: Value
  {Value.as_array(v) == Value.cases(~(_ => Value | (List<Value> & (List<Value> -> Value))), ~Inl{Value.null}, ~(b => Inl{Value.bool(b)}), ~(n => Inl{Value.number(n)}), ~(t => Inl{Value.string(t)}), ~(a => Inr{(a, Value.array)}), ~(o => Inl{Value.object(o)}), v) : Value | (List<Value> & (List<Value> -> Value))}

law Value.as_array.dup:
  for v: Value
  Value & Maybe<List<Value>>

law Value.as_array.dup.ok:
  for v: Value
  {Value.as_array.dup(v) == Value.cases(~(_ => Value & Maybe<List<Value>>), ~(Value.null, None{}), ~(b => (Value.bool(b), None{})), ~(n => (Value.number(n), None{})), ~(t => (Value.string(t), None{})), ~(a => (Value.array(a), Some{a})), ~(o => (Value.object(o), None{})), v) : Value & Maybe<List<Value>>}

law Value.as_array.era:
  for v: Value
  Maybe<List<Value>>

law Value.as_array.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<List<Value>>
  for h: {Value.as_array.dup(v) == (w, val) : Value & Maybe<List<Value>>}
  {val == Value.as_array.era(v) : Maybe<List<Value>>}

# Value.as_object(v) gives Inr with its members and a setter that puts new ones
# in their place when v is an object, and hands v back in Inl when it isn't.
# Value.as_object.dup(v) hands v back beside a copy of its members, and
# Value.as_object.era(v) gives the copy without v.
law Value.as_object:
  for v: Value
  Value | (List<(Text & Value)> & (List<(Text & Value)> -> Value))

law Value.as_object.ok:
  for v: Value
  {Value.as_object(v) == Value.cases(~(_ => Value | (List<(Text & Value)> & (List<(Text & Value)> -> Value))), ~Inl{Value.null}, ~(b => Inl{Value.bool(b)}), ~(n => Inl{Value.number(n)}), ~(t => Inl{Value.string(t)}), ~(a => Inl{Value.array(a)}), ~(o => Inr{(o, Value.object)}), v) : Value | (List<(Text & Value)> & (List<(Text & Value)> -> Value))}

law Value.as_object.dup:
  for v: Value
  Value & Maybe<List<(Text & Value)>>

law Value.as_object.dup.ok:
  for v: Value
  {Value.as_object.dup(v) == Value.cases(~(_ => Value & Maybe<List<(Text & Value)>>), ~(Value.null, None{}), ~(b => (Value.bool(b), None{})), ~(n => (Value.number(n), None{})), ~(t => (Value.string(t), None{})), ~(a => (Value.array(a), None{})), ~(o => (Value.object(o), Some{o})), v) : Value & Maybe<List<(Text & Value)>>}

law Value.as_object.era:
  for v: Value
  Maybe<List<(Text & Value)>>

law Value.as_object.era.ok:
  for v: Value
  for -w: Value
  for -val: Maybe<List<(Text & Value)>>
  for h: {Value.as_object.dup(v) == (w, val) : Value & Maybe<List<(Text & Value)>>}
  {val == Value.as_object.era(v) : Maybe<List<(Text & Value)>>}

# =========
# SPEC load
# =========

# load(s) hands s back beside the value s is the JSON text of, or None when s
# isn't JSON text. load.era(s) gives the same answer without handing s back.
law load:
  for s: String
  String & Maybe<Value>

law load.borrows:
  for s: String
  for -str: String
  for -val: Maybe<Value>
  for h: {load(s) == (str, val) : String & Maybe<Value>}
  {str == s : String}

law load.era:
  for s: String
  Maybe<Value>

law load.era.ok:
  for s: String
  for -str: String
  for -val: Maybe<Value>
  for h: {load(s) == (str, val) : String & Maybe<Value>}
  {val == load.era(s) : Maybe<Value>}

# A string that isn't JSON text loads to nothing.
law load.none:
  for s: String
  for h: {ABNF.matches.era(grammar, "JSON-text", s) == False{} : Bool}
  {load.era(s) == None{} : Maybe<Value>}

# JSON-text = ws value ws
law load.text:
  for w1: String
  for v: String
  for w2: String
  for h1: {ABNF.matches.era(grammar, "ws", w1) == True{} : Bool}
  for hv: {ABNF.matches.era(grammar, "value", v) == True{} : Bool}
  for h2: {ABNF.matches.era(grammar, "ws", w2) == True{} : Bool}
  {load.era(w1 ++ v ++ w2) == load.era(v) : Maybe<Value>}

# value = null
law load.null:
  for t: String
  for h: {ABNF.matches.era(grammar, "null", t) == True{} : Bool}
  {load.era(t) == Some{Value.null} : Maybe<Value>}

# value = true
law load.true:
  for t: String
  for h: {ABNF.matches.era(grammar, "true", t) == True{} : Bool}
  {load.era(t) == Some{Value.bool(True{})} : Maybe<Value>}

# value = false
law load.false:
  for t: String
  for h: {ABNF.matches.era(grammar, "false", t) == True{} : Bool}
  {load.era(t) == Some{Value.bool(False{})} : Maybe<Value>}

# value = number
law load.number:
  for n: String
  for h: {ABNF.matches.era(grammar, "number", n) == True{} : Bool}
  {load.era(n) == Some{Value.number(Number.make(n, h))} : Maybe<Value>}

# string = quotation-mark *char quotation-mark
law load.string:
  for q1: String
  for x: String
  for q2: String
  for hq1: {ABNF.matches.era(grammar, "quotation-mark", q1) == True{} : Bool}
  for hq2: {ABNF.matches.era(grammar, "quotation-mark", q2) == True{} : Bool}
  for hx: {ABNF.matches.era(grammar, "string", q1 ++ x ++ q2) == True{} : Bool}
  for hu: {Extra.String.is_unicode.era(decode.era(x)) == True{} : Bool}
  {load.era(q1 ++ x ++ q2) == Some{Value.string(Text.make(decode.era(x), hu))} : Maybe<Value>}

# array = begin-array [ value *( value-separator value ) ] end-array
law load.array.nil:
  for b: String
  for e: String
  for hb: {ABNF.matches.era(grammar, "begin-array", b) == True{} : Bool}
  for he: {ABNF.matches.era(grammar, "end-array", e) == True{} : Bool}
  {load.era(b ++ e) == Some{Value.array([])} : Maybe<Value>}

law load.array.one:
  for b: String
  for v: String
  for e: String
  for hb: {ABNF.matches.era(grammar, "begin-array", b) == True{} : Bool}
  for hv: {ABNF.matches.era(grammar, "value", v) == True{} : Bool}
  for he: {ABNF.matches.era(grammar, "end-array", e) == True{} : Bool}
  for x: Value
  for hx: {load.era(v) == Some{x} : Maybe<Value>}
  {load.era(b ++ v ++ e) == Some{Value.array([x])} : Maybe<Value>}

# After a comma, at least one more element follows.
law load.array.cons:
  for b: String
  for v: String
  for sep: String
  for rest: String
  for hb: {ABNF.matches.era(grammar, "begin-array", b) == True{} : Bool}
  for hv: {ABNF.matches.era(grammar, "value", v) == True{} : Bool}
  for hsep: {ABNF.matches.era(grammar, "value-separator", sep) == True{} : Bool}
  for x: Value
  for hx: {load.era(v) == Some{x} : Maybe<Value>}
  for x2: Value
  for xs: List<Value>
  for hr: {load.era(b ++ rest) == Some{Value.array(x2 <> xs)} : Maybe<Value>}
  {load.era(b ++ v ++ sep ++ rest) == Some{Value.array(x <> x2 <> xs)} : Maybe<Value>}

# object = begin-object [ member *( value-separator member ) ] end-object
# member = string name-separator value
law load.object.nil:
  for b: String
  for e: String
  for hb: {ABNF.matches.era(grammar, "begin-object", b) == True{} : Bool}
  for he: {ABNF.matches.era(grammar, "end-object", e) == True{} : Bool}
  {load.era(b ++ e) == Some{Value.object([])} : Maybe<Value>}

# A member's name is the string its key loads to.
law load.object.one:
  for b: String
  for k: String
  for n: String
  for v: String
  for e: String
  for hb: {ABNF.matches.era(grammar, "begin-object", b) == True{} : Bool}
  for hk: {ABNF.matches.era(grammar, "string", k) == True{} : Bool}
  for hn: {ABNF.matches.era(grammar, "name-separator", n) == True{} : Bool}
  for hv: {ABNF.matches.era(grammar, "value", v) == True{} : Bool}
  for he: {ABNF.matches.era(grammar, "end-object", e) == True{} : Bool}
  for key: Text
  for hkey: {load.era(k) == Some{Value.string(key)} : Maybe<Value>}
  for x: Value
  for hx: {load.era(v) == Some{x} : Maybe<Value>}
  {load.era(b ++ k ++ n ++ v ++ e) == Some{Value.object([(key, x)])} : Maybe<Value>}

# After a comma, at least one more member follows.
law load.object.cons:
  for b: String
  for k: String
  for n: String
  for v: String
  for sep: String
  for rest: String
  for hb: {ABNF.matches.era(grammar, "begin-object", b) == True{} : Bool}
  for hk: {ABNF.matches.era(grammar, "string", k) == True{} : Bool}
  for hn: {ABNF.matches.era(grammar, "name-separator", n) == True{} : Bool}
  for hv: {ABNF.matches.era(grammar, "value", v) == True{} : Bool}
  for hsep: {ABNF.matches.era(grammar, "value-separator", sep) == True{} : Bool}
  for key: Text
  for hkey: {load.era(k) == Some{Value.string(key)} : Maybe<Value>}
  for x: Value
  for hx: {load.era(v) == Some{x} : Maybe<Value>}
  for m: (Text & Value)
  for o: List<(Text & Value)>
  for hr: {load.era(b ++ rest) == Some{Value.object(m <> o)} : Maybe<Value>}
  {load.era(b ++ k ++ n ++ v ++ sep ++ rest) == Some{Value.object((key, x) <> m <> o)} : Maybe<Value>}

# =========
# SPEC dump
# =========

# dump(v) hands v back beside JSON text for v. dump.era(v) gives the same text
# without handing v back.
law dump:
  for v: Value
  Value & String

law dump.borrows:
  for v: Value
  for -val: Value
  for -str: String
  for h: {dump(v) == (val, str) : Value & String}
  {val == v : Value}

law dump.era:
  for v: Value
  String

law dump.era.ok:
  for v: Value
  for -val: Value
  for -str: String
  for h: {dump(v) == (val, str) : Value & String}
  {str == dump.era(v) : String}

# Loading what dump writes gives the value back.
law dump.load:
  for v: Value
  {load.era(dump.era(v)) == Some{v} : Maybe<Value>}
