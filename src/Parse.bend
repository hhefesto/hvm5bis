import Base
import ./Tm.bend as T

# hvm5bis: the parser, a port of the Parse section of HVM4's src/hvm.c.
#
# Meaning. A program is a list of definitions `@name = term` and
# `#include "file"`. parse_term reads one term of HVM4's surface syntax
# (docs/hvm/syntax.md) and answers its book term: a T.Tm whose variables
# are de Bruijn levels (BJV for lambda/let binders, BJ0/BJ1 for the two
# sides of a dup), with every sugar (cloned binders, forks, inline dups,
# lets, lists, strings, nats, chars, matches) already desugared exactly
# as hvm.c desugars it, including its auto-dup labels (a counter from
# 0x800000) and its affinity errors.
#
# Shape. Bend allows no mutual recursion, so hvm.c's mutually recursive
# parse_term_* functions are one def, pz, whose Sel argument says which
# of them (or which point inside one) runs; each case is one basic block
# of the C code, and a recursive call is pz(p, ..) on a smaller fuel p.
# The parser state St is plain data threaded by the P monad, which also
# carries the first parse error (PEr) out.

# State
# =====

# PBind: a binder in scope (hvm.c's PBind); side 2 stands for -1
type PB is Data:
  PB{name: U32, lvl: U32, lab: U32, forked: U32, cloned: U32, side: U32}

# a top-level definition, in the order read
type Df is Data:
  Df{id: U32, tm: T.Tm}

# src: the bytes not yet read; binds: innermost first; flab: the next
# fresh label; fside: PARSE_FORK_SIDE (2 = -1); tab/names/ntab: the name
# table (names newest first); book: the definitions, newest first
type St is Data:
  St{src: List<&2, U32>, binds: List<&2, PB>, flab: U32, fside: U32, tab: Map<&2, U32>, names: List<&2, String>, ntab: U32, book: List<&2, Df>}

def st.src(+s: St) -> List<&2, U32>:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      src

def st.binds(+s: St) -> List<&2, PB>:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      binds

def st.flab(+s: St) -> U32:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      flab

def st.fside(+s: St) -> U32:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      fside

def st.names(+s: St) -> List<&2, String>:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      names

def st.ntab(+s: St) -> U32:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      ntab

def st.book(+s: St) -> List<&2, Df>:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      book

def st.set_src(s: St, x: List<&2, U32>) -> St:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      St{x, binds, flab, fside, tab, names, ntab, book}

def st.set_binds(s: St, x: List<&2, PB>) -> St:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      St{src, x, flab, fside, tab, names, ntab, book}

def st.set_flab(s: St, +x: U32) -> St:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      St{src, binds, x, fside, tab, names, ntab, book}

def st.set_fside(s: St, +x: U32) -> St:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      St{src, binds, flab, x, tab, names, ntab, book}

def st.add_def(s: St, +id: U32, t: T.Tm) -> St:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      St{src, Nil{}, flab, fside, tab, names, ntab, Df{id, t} <> book}

# The monad
# =========

type PR<-X: Type> is Type:
  POk{st: St, x: X}
  PEr{e: String, at: List<&2, U32>}

def P(-X: Type) -> Type:
  St -> PR<X>

def P.pure(-X: Type, x: X) -> P(X):
  st => POk{st, x}

def P.go(-X: Type, -Y: Type, r: PR<X>, f: X -> P(Y)) -> PR<Y>:
  match r:
    case POk{st, x}:
      f(x, st)
    case PEr{e, at}:
      PEr{e, at}

def P.bind(-X: Type, -Y: Type, m: P(X), f: X -> P(Y)) -> P(Y):
  st => P.go(X, Y, m(st), f)

def P.get() -> P(St):
  +st => POk{st, st}

def P.put(st: St) -> P(Unit):
  old => POk{st, Unit{}}

def P.if(-X: Type, b: Bool, t: P(X), e: P(X)) -> P(X):
  match b:
    case True{}:
      t
    case False{}:
      e

def P.seq(-X: Type, a: P(Unit), b: P(X)) -> P(X):
  P.bind(Unit, X, a, u => b)

def P.unit() -> P(Unit):
  P.pure(Unit, Unit{})

def P.die(-X: Type, msg: String) -> P(X):
  +st => PEr{msg, st.src(st)}

# Bytes
# =====

def lx.hd(+s: List<&2, U32>) -> U32:
  match s:
    case Nil{}:
      0
    case Con{h, t}:
      h

def lx.tl(+s: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def lx.at(k: Nat, +s: List<&2, U32>) -> U32:
  match k:
    case 0n:
      lx.hd(s)
    case 1n+q:
      lx.at(q, lx.tl(s))

def lx.drop(k: Nat, +s: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      s
    case 1n+q:
      lx.drop(q, lx.tl(s))

def lx.is_end(+s: List<&2, U32>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# does s start with the bytes lit?
def lx.starts(lit: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  match lit:
    case Nil{}:
      True{}
    case Con{+h, t}:
      U32.is_eq(h, lx.hd(s)) && (U32.is_ne(h, 0) && lx.starts(t, lx.tl(s)))

def lx.len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+lx.len(t)

def lx.is_space(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9) || U32.is_eq(c, 10) || U32.is_eq(c, 13)

# parse_skip: whitespace and // line comments (cm: inside a comment;
# k: fuel, one per byte)
def lx.sk(k: Nat, cm: Bool, s: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      s
    case 1n+q:
      match cm:
        case True{}:
          match s:
            case Nil{}:
              Nil{}
            case Con{+h, t}:
              match h:
                case 10:
                  lx.sk(q, False{}, t)
                case x:
                  lx.sk(q, True{}, t)
        case False{}:
          match s:
            case Nil{}:
              Nil{}
            case Con{+h, t}:
              match h:
                case 32:
                  lx.sk(q, False{}, t)
                case 9:
                  lx.sk(q, False{}, t)
                case 10:
                  lx.sk(q, False{}, t)
                case 13:
                  lx.sk(q, False{}, t)
                case 47:
                  match t:
                    case Nil{}:
                      [47]
                    case Con{+h2, t2}:
                      match h2:
                        case 47:
                          lx.sk(q, True{}, t2)
                        case y:
                          47 <> (y <> t2)
                case x:
                  x <> t

def lx.skip(s: List<&2, U32>) -> List<&2, U32>:
  lx.sk(4294967295n, False{}, s)

def lx.is_digit(+c: U32) -> Bool:
  U32.is_le(48, c) && U32.is_le(c, 57)

def lx.is_init(+c: U32) -> Bool:
  (U32.is_le(97, c) && U32.is_le(c, 122)) || (U32.is_le(65, c) && U32.is_le(c, 90))

def lx.is_nick(+c: U32) -> Bool:
  lx.is_init(c) || lx.is_digit(c) || U32.is_eq(c, 95) || U32.is_eq(c, 36)

# nick_letter_to_b64
def lx.b64.dig(z: Bool, +c: U32) -> U32:
  match z:
    case True{}:
      (c - 48 + 53 : U32)
    case False{}:
      63

def lx.b64.up(z: Bool, +c: U32) -> U32:
  match z:
    case True{}:
      (c - 65 + 27 : U32)
    case False{}:
      lx.b64.dig(lx.is_digit(c), c)

def lx.b64.lo(z: Bool, +c: U32) -> U32:
  match z:
    case True{}:
      (c - 97 + 1 : U32)
    case False{}:
      lx.b64.up(U32.is_le(65, c) && U32.is_le(c, 90), c)

def lx.b64(+c: U32) -> U32:
  match c:
    case 95:
      0
    case x:
      lx.b64.lo(U32.is_le(97, x) && U32.is_le(x, 122), x)

# the nick characters at the head of s (f: the head is one)
def lx.name.go(k: Nat, f: Bool, +s: List<&2, U32>) -> List<&2, U32>:
  match k f:
    case 0n _:
      Nil{}
    case _ False{}:
      Nil{}
    case 1n+q True{}:
      lx.hd(s) <> lx.name.go(q, lx.is_nick(lx.hd(lx.tl(s))), lx.tl(s))

def lx.name(+s: List<&2, U32>) -> List<&2, U32>:
  lx.name.go(4294967295n, lx.is_nick(lx.hd(s)), s)

def lx.digits.go(k: Nat, f: Bool, +s: List<&2, U32>) -> List<&2, U32>:
  match k f:
    case 0n _:
      Nil{}
    case _ False{}:
      Nil{}
    case 1n+q True{}:
      lx.hd(s) <> lx.digits.go(q, lx.is_digit(lx.hd(lx.tl(s))), lx.tl(s))

def lx.digits(+s: List<&2, U32>) -> List<&2, U32>:
  lx.digits.go(4294967295n, lx.is_digit(lx.hd(s)), s)

# the decimal value of a digit list (wrapping as u32 does)
def lx.dec(ds: List<&2, U32>, +acc: U32) -> U32:
  match ds:
    case Nil{}:
      acc
    case Con{+d, t}:
      lx.dec(t, (acc * 10 + d - 48 : U32))

# a nick name's 24-bit number (only called on at most 4 characters)
def lx.nick(cs: List<&2, U32>, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      lx.nick(t, U32.or(U32.shln(acc, 6n), lx.b64(c)))

def lx.str(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Con{+b, t}:
      SCon{Chr{b}, lx.str(t)}

# one character of a char or string literal (parse_char_esc)
type CR is Data:
  CR{c: U32, rest: List<&2, U32>}

def lx.esc.map(+c: U32) -> U32:
  match c:
    case 110:
      10
    case 116:
      9
    case 114:
      13
    case 48:
      0
    case x:
      x

def lx.esc.bs(s: List<&2, U32>) -> Maybe<&2, CR>:
  match s:
    case Nil{}:
      None{}
    case Con{+c, t}:
      Some{CR{lx.esc.map(c), t}}

def lx.cont(+b: U32) -> U32:
  U32.and(b, 63)

def lx.pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def lx.utf8.cls(+b0: U32) -> U32:
  lx.pick(U32.is_lt(b0, 128), 1, lx.pick(U32.is_eq(U32.and(b0, 224), 192), 2, lx.pick(U32.is_eq(U32.and(b0, 240), 224), 3, lx.pick(U32.is_eq(U32.and(b0, 248), 240), 4, 1))))

def lx.utf8(+k: U32, +b0: U32, +s: List<&2, U32>) -> CR:
  match k:
    case 2:
      match s:
        case Con{+b1, t}:
          CR{U32.or(U32.shln(U32.and(b0, 31), 6n), lx.cont(b1)), t}
        case x:
          CR{b0, x}
    case 3:
      match s:
        case Con{+b1, Con{+b2, t}}:
          CR{U32.or(U32.or(U32.shln(U32.and(b0, 15), 12n), U32.shln(lx.cont(b1), 6n)), lx.cont(b2)), t}
        case x:
          CR{b0, x}
    case 4:
      match s:
        case Con{+b1, Con{+b2, Con{+b3, t}}}:
          CR{U32.or(U32.or(U32.shln(U32.and(b0, 7), 18n), U32.shln(lx.cont(b1), 12n)), U32.or(U32.shln(lx.cont(b2), 6n), lx.cont(b3))), t}
        case x:
          CR{b0, x}
    case j:
      CR{b0, s}

def lx.esc(s: List<&2, U32>) -> Maybe<&2, CR>:
  match s:
    case Nil{}:
      None{}
    case Con{+b, +t}:
      match b:
        case 92:
          lx.esc.bs(t)
        case x:
          Some{lx.utf8(lx.utf8.cls(x), x, t)}

# String literal bodies: the code points (reversed) up to the fence,
# and the bytes after it. SLAt: at s, f says s starts with the fence;
# SLGot: one character was just read
type CS is Data:
  CS{cs: List<&2, U32>, rest: List<&2, U32>}

type SL is Data:
  SLAt{s: List<&2, U32>, f: Bool}
  SLGot{r: Maybe<&2, CR>}

def lx.sl(k: Nat, +fence: U32, acc: List<&2, U32>, m: SL) -> Maybe<&2, CS>:
  match k m:
    case 0n _:
      None{}
    case 1n+q SLAt{+s, True{}}:
      Some{CS{acc, lx.tl(s)}}
    case 1n+q SLAt{+s, False{}}:
      lx.sl(q, fence, acc, SLGot{lx.esc(s)})
    case 1n+q SLGot{None{}}:
      None{}
    case 1n+q SLGot{Some{CR{c, +rest}}}:
      lx.sl(q, fence, c <> acc, SLAt{rest, U32.is_eq(lx.hd(rest), fence)})

# Monadic reading
# ===============

def P.src() -> P(List<&2, U32>):
  +st => POk{st, st.src(st)}

def P.setsrc(x: List<&2, U32>) -> P(Unit):
  st => POk{st.set_src(st, x), Unit{}}

def P.skip() -> P(Unit):
  +st => POk{st.set_src(st, lx.skip(st.src(st))), Unit{}}

def P.adv() -> P(Unit):
  +st => POk{st.set_src(st, lx.tl(st.src(st))), Unit{}}

def P.peek() -> P(U32):
  +st => POk{st, lx.hd(st.src(st))}

def P.try.go(z: Bool, +n: Nat, +st: St) -> PR<Bool>:
  match z:
    case True{}:
      POk{st.set_src(st, lx.drop(n, st.src(st))), True{}}
    case False{}:
      POk{st, False{}}

# parse_match: consume lit if the input starts with it
def P.try(+lit: List<&2, U32>) -> P(Bool):
  +st => P.try.go(lx.starts(lit, st.src(st)), lx.len(lit), st)

def P.sep.go(z: Bool, +st: St) -> PR<Bool>:
  match z:
    case True{}:
      POk{st.set_src(st, lx.tl(st.src(st))), True{}}
    case False{}:
      POk{st, False{}}

# parse_sep
def P.sep() -> P(Bool):
  +st => P.sep.go(U32.is_eq(lx.hd(st.src(st)), 44) || U32.is_eq(lx.hd(st.src(st)), 59), st)

def P.unitify(m: P(Bool)) -> P(Unit):
  P.bind(Bool, Unit, m, b => P.unit())

def lx.detected(+s: List<&2, U32>) -> String:
  match s:
    case Nil{}:
      "EOF"
    case Con{h, t}:
      "'" ++ lx.str([h]) ++ "'"
def lx.utf8.one(+s: List<&2, U32>) -> List<&2, U32>:
  [lx.hd(s)]

def P.red() -> String:
  String.from_list([Chr{27}, Chr{91}, Chr{49}, Chr{59}, Chr{51}, Chr{49}, Chr{109}]) ++ "PARSE_ERROR" ++ String.from_list([Chr{27}, Chr{91}, Chr{48}, Chr{109}, Chr{1}])

# parse_error: expected `what`, detected the next byte
def P.fail(-X: Type, what: String) -> P(X):
  +st => PEr{P.red() ++ "\n- expected: " ++ what ++ "\n- detected: " ++ lx.detected(st.src(st)), st.src(st)}

def P.need(b: Bool, what: String) -> P(Unit):
  match b:
    case True{}:
      P.unit()
    case False{}:
      P.fail(Unit, what)

# parse_consume
def P.consume(+lit: List<&2, U32>, what: String) -> P(Unit):
  do P<Unit>:
    P.skip()
    b : Bool <- P.try(lit)
    P.need(b, what)
    P.skip()

# Names
# =====

type SI is Data:
  SI{st: St, id: U32}

def tab.find.new(z: Bool, +key: String, +v: U32, s: St) -> SI:
  match z s:
    case True{} St{src, binds, flab, fside, tab, names, +ntab, book}:
      SI{St{src, binds, flab, fside, Map.set(&2, U32, tab, key, ntab), key <> names, (ntab + 1 : U32), book}, ntab}
    case False{} x:
      SI{x, v}

def tab.find.k(+key: String, r: Map<&2, U32> & U32, s: St) -> SI:
  (m, +v) = r
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      tab.find.new(U32.is_eq(v, 4294967295), key, v, St{src, binds, flab, fside, m, names, ntab, book})

# table_find: the name's id, a new one if it is new
def tab.find(+key: String, s: St) -> SI:
  match s:
    case St{src, binds, flab, fside, tab, names, ntab, book}:
      tab.find.k(key, Map.get(U32, 4294967295, tab, key), St{src, binds, flab, fside, Map.new(&2, U32), names, ntab, book})

def P.find.k(r: SI) -> PR<U32>:
  match r:
    case SI{st, id}:
      POk{st, id}

def P.find(+key: String) -> P(U32):
  st => P.find.k(tab.find(key, st))

# the initial state: ZER SUC NIL CON CHR are ids 0..4 (symbols_init)
def st.new.k(r: SI) -> St:
  match r:
    case SI{st, id}:
      st

def st.new(src: List<&2, U32>) -> St:
  s = {St{src, Nil{}, 8388608, 2, Map.new(&2, U32), Nil{}, 0, Nil{}} : St}
  st.new.k(tab.find("CHR", st.new.k(tab.find("CON", st.new.k(tab.find("NIL", st.new.k(tab.find("SUC", st.new.k(tab.find("ZER", s))))))))))

# parse_name (and parse_name_ref): a nick name's table id
def P.name() -> P(U32):
  do P<U32>:
    P.skip()
    +s : List<&2, U32> <- P.src()
    P.need(lx.is_init(lx.hd(s)), "name")
    P.setsrc(lx.drop(lx.len(lx.name(s)), s))
    +id : U32 <- P.find(lx.str(lx.name(s)))
    P.skip()
    return id

def P.name_num.chk.go(z: Bool, +cs: List<&2, U32>, +s: List<&2, U32>) -> P(Unit):
  match z:
    case True{}:
      P.seq(Unit, P.setsrc(lx.drop(4n, s)), P.die(Unit, P.red() ++ "\n- base64 name '" ++ lx.str(cs) ++ "' exceeds 24-bit limit (max 0xFFFFFF)"))
    case False{}:
      P.unit()

# parse_name_num stops at the character that overflows 24 bits (the 5th)
def P.name_num.chk(+cs: List<&2, U32>, +s: List<&2, U32>) -> P(Unit):
  P.name_num.chk.go(Nat.is_gt(lx.len(cs), 4n), cs, s)
def P.name_num() -> P(U32):
  do P<U32>:
    P.skip()
    +s : List<&2, U32> <- P.src()
    P.need(lx.is_init(lx.hd(s)), "name")
    P.name_num.chk(lx.name(s), s)
    P.setsrc(lx.drop(lx.len(lx.name(s)), s))
    P.skip()
    return lx.nick(lx.name(s), 0)

# PARSE_FRESH_LAB++
def P.fresh() -> P(U32):
  +st => POk{st.set_flab(st, (st.flab(st) + 1 : U32)), st.flab(st)}

def P.push(+b: PB) -> P(Unit):
  +st => POk{st.set_binds(st, b <> st.binds(st)), Unit{}}

def lx.popn(k: Nat, +bs: List<&2, PB>) -> List<&2, PB>:
  match k bs:
    case 0n x:
      x
    case 1n+q Nil{}:
      Nil{}
    case 1n+q Con{b, t}:
      lx.popn(q, t)

def P.pop(+k: Nat) -> P(Unit):
  +st => POk{st.set_binds(st, lx.popn(k, st.binds(st))), Unit{}}

def P.binds() -> P(List<&2, PB>):
  +st => POk{st, st.binds(st)}

def P.fside() -> P(U32):
  +st => POk{st, st.fside(st)}

def P.setside(+x: U32) -> P(Unit):
  +st => POk{st.set_fside(st, x), Unit{}}

# PBind constructors: parse_bind_push and parse_bind_push_side
def pb(+name: U32, +depth: U32, +lab: U32, +forked: U32, +cloned: U32) -> PB:
  PB{name, (depth + 1 : U32), lab, forked, cloned, 2}

def pb.side(+name: U32, +depth: U32, +lab: U32, +side: U32, +cloned: U32) -> PB:
  PB{name, (depth + 1 : U32), lab, 0, cloned, side}

# parse_auto_dup: uses > 1 takes uses - 1 fresh labels
def P.adup.go(z: Bool, +body: T.Tm, +lvl: U32, +base: U32, +tgt: U32, +ext: U32, +uses: U32) -> P(T.Tm):
  match z:
    case True{}:
      +st => POk{st.set_flab(st, (st.flab(st) + uses - 1 : U32)), T.tm.auto_dup(body, lvl, base, tgt, ext, uses, st.flab(st))}
    case False{}:
      P.pure(T.Tm, body)

def P.adup(+body: T.Tm, +lvl: U32, +base: U32, +tgt: U32, +ext: U32, +uses: U32) -> P(T.Tm):
  P.adup.go(U32.is_gt(uses, 1), body, lvl, base, tgt, ext, uses)

# the same when cl (the binder is cloned), else the body unchanged
def P.adup.c(+cl: U32, +body: T.Tm, +lvl: U32, +base: U32, +tgt: U32, +ext: U32, +uses: U32) -> P(T.Tm):
  P.adup.go(U32.is_ne(cl, 0) && U32.is_gt(uses, 1), body, lvl, base, tgt, ext, uses)

def st.name.of.k(r: Maybe<&2, String>) -> String:
  match r:
    case None{}:
      "?"
    case Some{s}:
      s

def st.name.of(k: Nat, +names: List<&2, String>) -> String:
  st.name.of.k(List.get(&2, String, names, k))
# the id's name (names is newest first)
def P.nameof(+id: U32) -> P(String):
  +st => POk{st, st.name.of(U32.to_nat((st.ntab(st) - 1 - id : U32)), st.names(st))}

# parse_error_affine, raised when bad
def P.affine(bad: Bool, +nam: U32, +sub: String, +uses: U32) -> P(Unit):
  match bad:
    case True{}:
      do P<Unit>:
        +n : String <- P.nameof(nam)
        P.die(Unit, P.red() ++ "\n- variable '" ++ n ++ sub ++ "' used " ++ U32.show(uses) ++ " times\n- hint: declare variable as '&" ++ n ++ "' to allow multiple uses")
    case False{}:
      P.unit()

def P.affine1(+cl: U32, +nam: U32, +sub: String, +uses: U32) -> P(Unit):
  P.affine(U32.is_eq(cl, 0) && U32.is_gt(uses, 1), nam, sub, uses)

# Pure helpers for the parser
# ===========================

def u.pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def u.b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def L.lam() -> List<&2, U32>:
  [206, 187]

def L.inc() -> List<&2, U32>:
  [226, 134, 145]

def L.s0() -> List<&2, U32>:
  [226, 130, 128]

def L.s1() -> List<&2, U32>:
  [226, 130, 129]

def L.amp0() -> List<&2, U32>:
  [38, 226, 130, 128]

def L.amp1() -> List<&2, U32>:
  [38, 226, 130, 129]

def L.include() -> List<&2, U32>:
  [35, 105, 110, 99, 108, 117, 100, 101]

def is.c(+s: List<&2, U32>, +c: U32) -> Bool:
  U32.is_eq(lx.hd(s), c)

# what parse_term_atom sees first (1 λ, 2 !, 3 &, 4 #, 5 @, 6 ^, 7 ↑,
# 8 *, 9 (, 10 [, 11 ', 12 a string, 13 a digit, 0 a variable)
def atom.kind(+s: List<&2, U32>) -> U32:
  u.pick(lx.starts(L.lam(), s), 1, u.pick(is.c(s, 33), 2, u.pick(is.c(s, 38), 3, u.pick(is.c(s, 35), 4, u.pick(is.c(s, 64), 5, u.pick(is.c(s, 94), 6, u.pick(lx.starts(L.inc(), s), 7, u.pick(is.c(s, 42), 8, u.pick(is.c(s, 40), 9, u.pick(is.c(s, 91), 10, u.pick(is.c(s, 39), 11, u.pick(is.c(s, 34) || is.c(s, 96), 12, u.pick(lx.is_digit(lx.hd(s)), 13, 0)))))))))))))

def atom.drop.k(z: Bool) -> Nat:
  match z:
    case True{}:
      1n
    case False{}:
      0n

# the bytes parse_match consumes for that kind
def atom.drop(+k: U32) -> Nat:
  match k:
    case 0:
      0n
    case 1:
      2n
    case 7:
      3n
    case x:
      atom.drop.k(U32.is_le(x, 9))

def opr.peek1(+c: U32) -> U32:
  match c:
    case 43:
      0
    case 45:
      1
    case 42:
      2
    case 47:
      3
    case 37:
      4
    case 94:
      7
    case 126:
      10
    case 60:
      13
    case 62:
      15
    case x:
      255

# parse_term_opr_peek: an OP2 code, 255 for none
def opr.peek(+s: List<&2, U32>) -> U32:
  u.pick(lx.starts([61, 61], s), 11, u.pick(lx.starts([33, 61], s), 12, u.pick(lx.starts([60, 61], s), 14, u.pick(lx.starts([62, 61], s), 16, u.pick(lx.starts([60, 60], s), 8, u.pick(lx.starts([62, 62], s), 9, u.pick(lx.starts([38, 38], s), 5, u.pick(lx.starts([124, 124], s), 6, opr.peek1(lx.hd(s))))))))))

def opr.len(+op: U32) -> Nat:
  match op:
    case 11:
      2n
    case 12:
      2n
    case 14:
      2n
    case 16:
      2n
    case 8:
      2n
    case 9:
      2n
    case 5:
      2n
    case 6:
      2n
    case x:
      1n

# parse_term_opr_prec
def opr.prec(+op: U32) -> U32:
  match op:
    case 6:
      1
    case 5:
      2
    case 11:
      3
    case 12:
      3
    case 13:
      4
    case 14:
      4
    case 15:
      4
    case 16:
      4
    case 8:
      5
    case 9:
      5
    case 0:
      6
    case 1:
      6
    case 2:
      7
    case 3:
      7
    case 4:
      7
    case 7:
      8
    case x:
      0

# what parse_term_app_prec sees (1 <>, 2 ===, 3 .&., 4 .|., 5 an
# operator binding at least mp, 6 a call, 0 nothing more)
def app.kind(+s: List<&2, U32>, +mp: U32) -> U32:
  u.pick(lx.starts([60, 62], s), 1, u.pick(lx.starts([61, 61, 61], s), 2, u.pick(lx.starts([46, 38, 46], s), 3, u.pick(lx.starts([46, 124, 46], s), 4, u.pick(U32.is_ne(opr.peek(s), 255) && U32.is_ge(opr.prec(opr.peek(s)), mp), 5, u.pick(is.c(s, 40), 6, 0))))))

# a match case head: 1 a char, 2 digits, 3 #Name, 4 [], 5 <>, 0 none
def case.kind(+s: List<&2, U32>) -> U32:
  u.pick(is.c(s, 39), 1, u.pick(lx.is_digit(lx.hd(s)), 2, u.pick(is.c(s, 35), 3, u.pick(lx.starts([91, 93], s), 4, u.pick(lx.starts([60, 62], s), 5, 0)))))

# after the digits of a case (r: the bytes after them, skipped):
# 1 a switch N:, 2 0n, 3 1n+, 0 not a case
def case.digk(+ext: U32, +r: List<&2, U32>) -> U32:
  u.pick(is.c(r, 58), 1, u.pick(is.c(r, 110), u.pick(U32.is_eq(ext, 0) && U32.is_ne(lx.at(1n, r), 43), 2, u.pick(U32.is_eq(ext, 1) && U32.is_eq(lx.at(1n, r), 43), 3, 0)), 0))

def dup.patk.go(+s: List<&2, U32>) -> U32:
  u.pick(is.c(s, 40), 1, u.pick(is.c(s, 123), 2, u.pick(lx.is_init(lx.hd(s)) && is.c(lx.skip(lx.drop(lx.len(lx.name(s)), s)), 123), 3, 0)))

# the dup-pattern head after `!`: 1 &(lab){, 2 &{, 3 &L{, 0 not one
def dup.patk(+s: List<&2, U32>) -> U32:
  u.pick(is.c(s, 38), dup.patk.go(lx.skip(lx.tl(s))), 0)

def sup.k2(+s: List<&2, U32>) -> U32:
  u.pick(lx.starts(L.lam(), s), 1, u.pick(is.c(s, 33) && U32.is_eq(lx.at(1n, s), 123), 2, u.pick(is.c(s, 91), 3, 0)))

# Term builders
# =============

def nil() -> T.Tm:
  T.Tl{13, 2, 0}

def con(a: T.Tm, b: T.Tm) -> T.Tm:
  T.tm.two(15, 3, a, b)

def chr(+c: U32) -> T.Tm:
  T.tm.one(14, 4, T.tm.num(c))

def nat.wrap(k: Nat, t: T.Tm) -> T.Tm:
  match k:
    case 0n:
      t
    case 1n+q:
      T.tm.one(14, 1, nat.wrap(q, t))

def str.build(cs: List<&2, U32>, tail: T.Tm) -> T.Tm:
  match cs:
    case Nil{}:
      tail
    case Con{+c, t}:
      str.build(t, con(chr(c), tail))

def lst.build(es: List<&2, T.Tm>, tail: T.Tm) -> T.Tm:
  match es:
    case Nil{}:
      tail
    case Con{e, t}:
      lst.build(t, con(e, tail))

def kids.of(es: List<&2, T.Tm>, acc: T.Tm) -> T.Tm:
  match es:
    case Nil{}:
      acc
    case Con{e, t}:
      kids.of(t, T.Tc{e, acc})

type Cs is Data:
  Cs{tag: U32, ext: U32, val: T.Tm}

# a match chain: the newest case innermost, over tail
def mat.chain(acc: List<&2, Cs>, tail: T.Tm) -> T.Tm:
  match acc:
    case Nil{}:
      tail
    case Con{Cs{tag, ext, val}, t}:
      mat.chain(t, T.tm.two(tag, ext, val, tail))

def lam.ext(+base: U32, z: Bool) -> U32:
  match z:
    case True{}:
      U32.or(base, 8388608)
    case False{}:
      base

def let.lam(+strict: U32, l: T.Tm) -> T.Tm:
  match strict:
    case 0:
      l
    case x:
      T.tm.use(l)

def sup.mk(+dyn: U32, lt: T.Tm, +lab: U32, a: T.Tm, b: T.Tm) -> T.Tm:
  match dyn:
    case 0:
      T.tm.sup(lab, a, b)
    case x:
      T.tm.dsu(lt, a, b)

# Binders
# =======

type LK is Data:
  LkF{b: PB}
  LkN{skipped: U32}

# parse_bind_lookup on one binder: 0 another name, 1 skipped, 2 found
def bd.class(+b: PB, +name: U32, +side: U32) -> U32:
  match b:
    case PB{+n, lvl, +lab, +forked, cloned, +bs}:
      u.pick(U32.is_ne(n, name), 0, u.pick(U32.is_lt(bs, 2), u.pick(U32.is_ne(side, 2), 1, 2), u.pick(U32.is_eq(side, 2) && U32.is_ne(lab, 0) && U32.is_eq(forked, 0), 1, u.pick(U32.is_ne(side, 2) && U32.is_eq(lab, 0), 1, 2))))

def bd.pick(+c: U32, +b: PB, r: LK) -> LK:
  match c:
    case 2:
      LkF{b}
    case x:
      r

def bd.look(bs: List<&2, PB>, +name: U32, +side: U32, +sk: U32) -> LK:
  match bs:
    case Nil{}:
      LkN{sk}
    case Con{+b, t}:
      bd.pick(bd.class(b, name, side), b, bd.look(t, name, side, U32.or(sk, u.b2u(U32.is_eq(bd.class(b, name, side), 1)))))

# parse_term_var's term for a found binder
def var.tm.k(z: Bool, +lvl: U32, +lab: U32, +side: U32) -> T.Tm:
  match z:
    case True{}:
      T.tm.bjv((lvl + u.b2u(U32.is_eq(side, 1)) : U32))
    case False{}:
      T.Tl{u.pick(U32.is_eq(side, 0), 43, u.pick(U32.is_eq(side, 1), 44, 42)), lab, lvl}

def var.tm(+b: PB, +side: U32, +fs: U32) -> T.Tm:
  match b:
    case PB{n, +lvl, +lab, +forked, cl, +bs}:
      var.tm.k(U32.is_eq(lab, 16777215), lvl, lab, u.pick(U32.is_eq(side, 2), u.pick(U32.is_lt(bs, 2), bs, u.pick(U32.is_ne(forked, 0), fs, 2)), side))

# the binders a fork pushes, in push order
def fork.binds(names: List<&2, U32>, +i: U32, +d: U32, +dd: U32, +lab: U32) -> List<&2, PB>:
  match names:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      pb(n, (d + i * dd + 1 : U32), lab, 1, 0) <> fork.binds(t, (i + 1 : U32), d, dd, lab)

def fork.bad1(+dyn: U32, +lvl: U32, +lab: U32, +l: T.Tm, +r: T.Tm) -> Bool:
  match dyn:
    case 0:
      U32.is_gt(T.tm.uses(l, lvl, 43, lab), 1) || U32.is_gt(T.tm.uses(r, lvl, 44, lab), 1)
    case x:
      U32.is_gt(T.tm.uses(l, lvl, 42, 0), 1) || U32.is_gt(T.tm.uses(r, (lvl + 1 : U32), 42, 0), 1)

# the fork's affinity check (as hvm.c computes it)
def fork.bad(names: List<&2, U32>, +i: U32, +d: U32, +dd: U32, +dyn: U32, +lab: U32, +l: T.Tm, +r: T.Tm) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{n, t}:
      fork.bad1(dyn, (d + i * dd + 1 : U32), lab, l, r) || fork.bad(t, (i + 1 : U32), d, dd, dyn, lab, l, r)

def fork.wrap1(+dyn: U32, +dd: U32, +lt: T.Tm, +lab: U32, body: T.Tm) -> T.Tm:
  match dyn:
    case 0:
      T.tm.lam((dd + 1 : U32), T.tm.dup(lab, T.tm.bjv((dd + 1 : U32)), body))
    case x:
      T.tm.lam((dd + 1 : U32), T.tm.ddu(lt, T.tm.bjv((dd + 1 : U32)), T.tm.lam((dd + 2 : U32), T.tm.lam((dd + 3 : U32), body))))

# the fork's binders, innermost (i = n - 1) first
def fork.wrap(k: Nat, +i: U32, +d: U32, +dd: U32, +dyn: U32, +lt: T.Tm, +lab: U32, body: T.Tm) -> T.Tm:
  match k:
    case 0n:
      body
    case 1n+q:
      fork.wrap(q, (i - 1 : U32), d, dd, dyn, lt, lab, fork.wrap1(dyn, (d + i * dd : U32), lt, lab, body))

# a captured variable of a sup-fork: its name, the term that refers to
# it outside (tag, lab, depth) and whether it is cloned
type FV is Data:
  FV{name: U32, depth: U32, tag: U32, lab: U32, cloned: U32}

def fv.of.side(dyn: Bool, +name: U32, +cl: U32, +lvl: U32, +lab: U32, +bs: U32) -> FV:
  match dyn:
    case True{}:
      FV{name, (lvl + bs : U32), 42, 0, cl}
    case False{}:
      FV{name, lvl, u.pick(U32.is_eq(bs, 0), 43, 44), lab, cl}

def fv.of.k(sided: Bool, frk: Bool, +name: U32, +cl: U32, +saved: U32, +lvl: U32, +lab: U32, +bs: U32) -> FV:
  match sided frk:
    case True{} _:
      fv.of.side(U32.is_eq(lab, 16777215), name, cl, lvl, lab, bs)
    case False{} True{}:
      FV{name, lvl, u.pick(U32.is_eq(saved, 0), 43, 44), lab, cl}
    case False{} False{}:
      FV{name, lvl, 42, 0, cl}

def fv.of(+b: PB, +name: U32, +cl: U32, +saved: U32) -> FV:
  match b:
    case PB{n, +lvl, +lab, +forked, c, +bs}:
      fv.of.k(U32.is_lt(bs, 2), U32.is_ne(forked, 0) && U32.is_lt(saved, 2), name, cl, saved, lvl, lab, bs)

def fv.name(+v: FV) -> U32:
  match v:
    case FV{name, depth, tag, lab, cloned}:
      name

def fv.cl(+v: FV) -> U32:
  match v:
    case FV{name, depth, tag, lab, cloned}:
      cloned

def fc.binds(fvs: List<&2, FV>, +i: U32, +d: U32, +d2: U32, +lab: U32) -> List<&2, PB>:
  match fvs:
    case Nil{}:
      Nil{}
    case Con{+v, t}:
      pb(fv.name(v), (d + i * d2 : U32), lab, 1, fv.cl(v)) <> fc.binds(t, (i + 1 : U32), d, d2, lab)

def fc.wrap1(+dyn: U32, v: T.Tm, +b: U32, +lt: T.Tm, +lab: U32, body: T.Tm) -> T.Tm:
  match dyn:
    case 0:
      T.tm.dup(lab, v, body)
    case x:
      T.tm.ddu(lt, v, T.tm.lam((b + 1 : U32), T.tm.lam((b + 2 : U32), body)))

def fc.wrap(fvs: List<&2, FV>, +i: U32, +d: U32, +d2: U32, +dyn: U32, +lt: T.Tm, +lab: U32, body: T.Tm) -> T.Tm:
  match fvs:
    case Nil{}:
      body
    case Con{FV{n, +depth, +tag, +flab, c}, t}:
      fc.wrap(t, (i - 1 : U32), d, d2, dyn, lt, lab, fc.wrap1(dyn, T.Tl{tag, flab, depth}, (d + i * d2 : U32), lt, lab, body))

def af.has(fvs: List<&2, FV>, +name: U32) -> Bool:
  match fvs:
    case Nil{}:
      False{}
    case Con{+v, t}:
      U32.is_eq(fv.name(v), name) || af.has(t, name)

def af.repl.k(z: Bool, +w: FV, +v: FV, rest: List<&2, FV>) -> List<&2, FV>:
  match z:
    case True{}:
      v <> rest
    case False{}:
      w <> rest

def af.repl(fvs: List<&2, FV>, +v: FV) -> List<&2, FV>:
  match fvs:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      af.repl.k(U32.is_eq(fv.name(w), fv.name(v)), w, v, af.repl(t, v))

def af.add(z: Bool, +fvs: List<&2, FV>, +v: FV) -> List<&2, FV>:
  match z:
    case True{}:
      af.repl(fvs, v)
    case False{}:
      List.append(&2, FV, fvs, [v])

def af.raw(+b: PB) -> Bool:
  match b:
    case PB{n, lvl, +lab, +forked, cl, +bs}:
      U32.is_ne(lab, 0) && U32.is_eq(forked, 0) && U32.is_eq(bs, 2)

def af.bname(+b: PB) -> U32:
  match b:
    case PB{n, lvl, lab, forked, cl, bs}:
      n

def af.one(z: Bool, +b: PB, +saved: U32, +acc: List<&2, FV>) -> List<&2, FV>:
  match z:
    case True{}:
      acc
    case False{}:
      af.add(af.has(acc, af.bname(b)), acc, fv.of(b, af.bname(b), 1, saved))

# auto-fork: every binder in scope but raw dups, oldest first, the
# innermost binding of a name kept in its first slot, all cloned
def af.collect(bs: List<&2, PB>, +acc: List<&2, FV>, +saved: U32) -> List<&2, FV>:
  match bs:
    case Nil{}:
      acc
    case Con{+b, t}:
      af.collect(t, af.one(af.raw(b), b, saved, acc), saved)

type LR is Data:
  LR{l: T.Tm, r: T.Tm}

def lr.l(+x: LR) -> T.Tm:
  match x:
    case LR{l, r}:
      l

def lr.r(+x: LR) -> T.Tm:
  match x:
    case LR{l, r}:
      r

def lst.is_nil(+xs: List<&2, Cs>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def u.len(-A: Data, xs: List<&2, A>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (1 + u.len(A, t) : U32)

def lx.until.go(k: Nat, f: Bool, +s: List<&2, U32>) -> List<&2, U32>:
  match k f:
    case 0n _:
      Nil{}
    case _ False{}:
      Nil{}
    case 1n+q True{}:
      lx.hd(s) <> lx.until.go(q, U32.is_ne(lx.hd(lx.tl(s)), 34) && U32.is_ne(lx.hd(lx.tl(s)), 0), lx.tl(s))

# the bytes up to the next `"`
def lx.until(+s: List<&2, U32>) -> List<&2, U32>:
  lx.until.go(4294967295n, U32.is_ne(lx.hd(s), 34) && U32.is_ne(lx.hd(s), 0), s)

# Monadic helpers that do not parse terms
# ======================================

def P.pushes(bs: List<&2, PB>) -> P(Unit):
  match bs:
    case Nil{}:
      P.unit()
    case Con{+b, t}:
      P.seq(Unit, P.push(b), P.pushes(t))

def P.optside(+lit: List<&2, U32>) -> P(Unit):
  do P<Unit>:
    b : Bool <- P.try(lit)
    P.if(Unit, b, P.seq(Unit, P.skip(), P.consume([58], ":")), P.unit())

def P.tamp() -> P(U32):
  do P<U32>:
    P.skip()
    +s : List<&2, U32> <- P.src()
    P.if(U32, is.c(s, 38), P.seq(U32, P.adv(), P.seq(U32, P.skip(), P.pure(U32, 1))), P.pure(U32, 0))

def P.sepu() -> P(Unit):
  P.unitify(P.sep())

def P.charlit.go(r: Maybe<&2, CR>) -> P(U32):
  match r:
    case None{}:
      P.fail(U32, "character")
    case Some{CR{+c, +rest}}:
      do P<U32>:
        P.setsrc(rest)
        P.need(U32.is_eq(lx.hd(rest), 39), "'")
        P.adv()
        return c

# parse_char_lit (at the opening quote)
def P.charlit() -> P(U32):
  do P<U32>:
    P.adv()
    +s : List<&2, U32> <- P.src()
    P.charlit.go(lx.esc(s))

def P.str.go(r: Maybe<&2, CS>) -> P(T.Tm):
  match r:
    case None{}:
      P.fail(T.Tm, "character")
    case Some{CS{cs, rest}}:
      P.seq(T.Tm, P.setsrc(rest), P.pure(T.Tm, str.build(cs, nil())))

def P.varerr.msg(dup: Bool, sk: Bool, +n: String) -> String:
  match dup sk:
    case True{} True{}:
      "\n- dup variable '" ++ n ++ "' requires subscript ₀ or ₁"
    case False{} True{}:
      "\n- non-dup variable '" ++ n ++ "' must be used without subscript (₀ or ₁)"
    case _ False{}:
      "\n- undefined variable '" ++ n ++ "'"

# parse_error_var
def P.varerr(+nam: U32, +side: U32, +sk: U32) -> P(T.Tm):
  do P<T.Tm>:
    +n : String <- P.nameof(nam)
    P.die(T.Tm, P.red() ++ P.varerr.msg(U32.is_eq(side, 2), U32.is_ne(sk, 0), n))

def P.var.go(r: LK, +nam: U32, +side: U32, +fs: U32) -> P(T.Tm):
  match r:
    case LkF{b}:
      P.pure(T.Tm, var.tm(b, side, fs))
    case LkN{sk}:
      P.varerr(nam, side, sk)

def P.fv.go(r: LK, +nam: U32, +cl: U32, +saved: U32) -> P(FV):
  match r:
    case LkF{b}:
      P.pure(FV, fv.of(b, nam, cl, saved))
    case LkN{sk}:
      P.bind(T.Tm, FV, P.varerr(nam, 2, sk), t => P.die(FV, ""))

# the sup-fork's per-variable affinity checks and auto-dups
def P.fcpost(fvs: List<&2, FV>, +i: U32, +d: U32, +d2: U32, +dyn: U32, +lab: U32, +bd: U32, +l: T.Tm, +r: T.Tm) -> P(LR):
  match fvs:
    case Nil{}:
      P.pure(LR, LR{l, r})
    case Con{FV{+nam, depth, tag, flab, +cl}, t}:
      do P<LR>:
        +lvl : U32 = (d + i * d2 + 1 : U32)
        +u0 : U32 = T.tm.uses(l, lvl, u.pick(U32.is_eq(dyn, 0), 43, 42), u.pick(U32.is_eq(dyn, 0), lab, 0))
        +u1 : U32 = T.tm.uses(r, (lvl + u.pick(U32.is_eq(dyn, 0), 0, 1) : U32), u.pick(U32.is_eq(dyn, 0), 44, 42), u.pick(U32.is_eq(dyn, 0), lab, 0))
        +l2 : T.Tm <- P.adup.c(cl, l, lvl, bd, u.pick(U32.is_eq(dyn, 0), 43, 42), u.pick(U32.is_eq(dyn, 0), lab, 0), u0)
        +r2 : T.Tm <- P.adup.c(cl, r, (lvl + u.pick(U32.is_eq(dyn, 0), 0, 1) : U32), bd, u.pick(U32.is_eq(dyn, 0), 44, 42), u.pick(U32.is_eq(dyn, 0), lab, 0), u1)
        P.affine1(cl, nam, "₀", u0)
        P.affine1(cl, nam, "₁", u1)
        P.fcpost(t, (i + 1 : U32), d, d2, dyn, lab, bd, l2, r2)

def P.clear() -> P(Unit):
  +st => POk{st.set_binds(st, Nil{}), Unit{}}

def P.adddef(+id: U32, t: T.Tm) -> P(Unit):
  st => POk{st.add_def(st, id, t), Unit{}}

# Small monadic helpers for the term parser
# ========================================

# does the input start with byte c?
def P.at(+c: U32) -> P(Bool):
  +st => POk{st, is.c(st.src(st), c)}

# parse_match(lit) when b is false; false (nothing read) when b is true
def P.try.if(b: Bool, +lit: List<&2, U32>) -> P(Bool):
  match b:
    case True{}:
      P.pure(Bool, False{})
    case False{}:
      P.try(lit)

# the sentinel parse_term_dup_pat answers when it saw no dup pattern
def sent() -> T.Tm:
  T.Tl{255, 0, 0}

def is.sent(+t: T.Tm) -> Bool:
  match t:
    case T.Tl{+tag, e, v}:
      U32.is_eq(tag, 255)
    case x:
      False{}

def dummy() -> T.Tm:
  T.Tl{0, 0, 0}

type NC is Data:
  NC{n: U32, cl: U32}

def pr.fst(+p: NC) -> U32:
  match p:
    case NC{n, cl}:
      n

def pr.snd(+p: NC) -> U32:
  match p:
    case NC{n, cl}:
      cl

# the head of a match case: none, or (tag, ext)
type CH is Data:
  CHNo{}
  CHYes{tag: U32, ext: U32}

def P.case.dig(+dk: U32, +v: U32, +r: List<&2, U32>) -> P(CH):
  match dk:
    case 1:
      P.seq(CH, P.setsrc(r), P.pure(CH, CHYes{31, v}))
    case 2:
      P.seq(CH, P.setsrc(lx.tl(r)), P.pure(CH, CHYes{12, 0}))
    case 3:
      P.seq(CH, P.setsrc(lx.drop(2n, r)), P.pure(CH, CHYes{12, 1}))
    case x:
      P.pure(CH, CHNo{})

def P.case.k(+k: U32, +s: List<&2, U32>) -> P(CH):
  match k:
    case 1:
      do P<CH>:
        +c : U32 <- P.charlit()
        P.skip()
        return CHYes{31, c}
    case 2:
      +ds = lx.digits(s)
      +r = lx.skip(lx.drop(lx.len(ds), s))
      P.case.dig(case.digk(lx.dec(ds, 0), r), lx.dec(ds, 0), r)
    case 3:
      do P<CH>:
        P.adv()
        +n : U32 <- P.name()
        return CHYes{12, n}
    case 4:
      P.seq(CH, P.setsrc(lx.drop(2n, s)), P.pure(CH, CHYes{12, 2}))
    case 5:
      P.seq(CH, P.setsrc(lx.drop(2n, s)), P.pure(CH, CHYes{12, 3}))
    case x:
      P.pure(CH, CHNo{})

# the head of a match case at s (it reads it when there is one)
def P.case(+s: List<&2, U32>) -> P(CH):
  P.case.k(case.kind(s), s)

# a fork's binder names after the first: `,y,z` up to `{`
def P.fname.step3() -> P(Maybe<&2, U32>):
  do P<Maybe<&2, U32>>:
    +n : U32 <- P.name()
    P.skip()
    return Some{n}

def P.fname.step2() -> P(Maybe<&2, U32>):
  do P<Maybe<&2, U32>>:
    P.sepu()
    P.skip()
    +b : Bool <- P.at(123)
    P.if(Maybe<&2, U32>, b, P.pure(Maybe<&2, U32>, None{}), P.fname.step3())

def P.fname.step() -> P(Maybe<&2, U32>):
  do P<Maybe<&2, U32>>:
    +b : Bool <- P.at(123)
    P.if(Maybe<&2, U32>, b, P.pure(Maybe<&2, U32>, None{}), P.fname.step2())

def P.fnames(k: Nat, r: Maybe<&2, U32>, +acc: List<&2, U32>) -> P(List<&2, U32>):
  match k r:
    case 0n _:
      P.pure(List<&2, U32>, List.reverse(&2, U32, acc))
    case _ None{}:
      P.pure(List<&2, U32>, List.reverse(&2, U32, acc))
    case 1n+q Some{+n}:
      P.bind(Maybe<&2, U32>, List<&2, U32>, P.fname.step(), r2 => P.fnames(q, r2, n <> acc))

# a sup-fork's captured variable: `&x` or `x`, then a separator
def P.sfv.step2(+saved: U32) -> P(Maybe<&2, FV>):
  do P<Maybe<&2, FV>>:
    P.skip()
    +cl : U32 <- P.tamp()
    +nam : U32 <- P.name()
    P.skip()
    +bs : List<&2, PB> <- P.binds()
    +v : FV <- P.fv.go(bd.look(bs, nam, 2, 0), nam, cl, saved)
    P.skip()
    P.sepu()
    return Some{v}

def P.sfv.step(+saved: U32) -> P(Maybe<&2, FV>):
  do P<Maybe<&2, FV>>:
    +b : Bool <- P.at(93)
    P.if(Maybe<&2, FV>, b, P.pure(Maybe<&2, FV>, None{}), P.sfv.step2(saved))

def P.sfvs(k: Nat, +saved: U32, r: Maybe<&2, FV>, +acc: List<&2, FV>) -> P(List<&2, FV>):
  match k r:
    case 0n _:
      P.pure(List<&2, FV>, List.reverse(&2, FV, acc))
    case _ None{}:
      P.pure(List<&2, FV>, List.reverse(&2, FV, acc))
    case 1n+q Some{+v}:
      P.bind(Maybe<&2, FV>, List<&2, FV>, P.sfv.step(saved), r2 => P.sfvs(q, saved, r2, v <> acc))

# a dup pattern's binder: (name, cloned)
def P.patname() -> P(NC):
  do P<NC>:
    P.skip()
    +cl : U32 <- P.tamp()
    +n : U32 <- P.name()
    return NC{n, cl}

# the static fork's affinity checks (at hvm.c's levels)
def P.forkchk(names: List<&2, U32>, +i: U32, +d: U32, +dd: U32, +dyn: U32, +lab: U32, +l: T.Tm, +r: T.Tm) -> P(Unit):
  match names:
    case Nil{}:
      P.unit()
    case Con{+n, t}:
      +lvl = (d + i * dd + 1 : U32)
      +u0 = T.tm.uses(l, lvl, u.pick(U32.is_eq(dyn, 0), 43, 42), u.pick(U32.is_eq(dyn, 0), lab, 0))
      +u1 = T.tm.uses(r, (lvl + u.pick(U32.is_eq(dyn, 0), 0, 1) : U32), u.pick(U32.is_eq(dyn, 0), 44, 42), u.pick(U32.is_eq(dyn, 0), lab, 0))
      P.seq(Unit, P.affine(U32.is_gt(u0, 1), n, "₀", u0), P.seq(Unit, P.affine(U32.is_gt(u1, 1), n, "₁", u1), P.forkchk(t, (i + 1 : U32), d, dd, dyn, lab, l, r)))

# the end of an inline-dup lambda λx&L / λx&(L): checks, auto-dups, term
def P.lami.fin(+cl: U32, +nam: U32, +d: U32, +dyn: U32, +lt: T.Tm, +lab: U32, +body: T.Tm) -> P(T.Tm):
  match dyn:
    case 0:
      do P<T.Tm>:
        +u0 : U32 = T.tm.uses(body, (d + 2 : U32), 43, lab)
        +u1 : U32 = T.tm.uses(body, (d + 2 : U32), 44, lab)
        +b1 : T.Tm <- P.adup.c(cl, body, (d + 2 : U32), (d + 2 : U32), 44, lab, u1)
        +b2 : T.Tm <- P.adup.c(cl, b1, (d + 2 : U32), (d + 2 : U32), 43, lab, u0)
        P.affine1(cl, nam, "₀", u0)
        P.affine1(cl, nam, "₁", u1)
        return T.tm.lam(lam.ext((d + 1 : U32), U32.is_eq(u0, 0) && U32.is_eq(u1, 0)), T.tm.dup(lab, T.tm.bjv((d + 1 : U32)), b2))
    case x:
      do P<T.Tm>:
        +u0 : U32 = T.tm.uses(body, (d + 2 : U32), 42, 0)
        +u1 : U32 = T.tm.uses(body, (d + 3 : U32), 42, 0)
        +b1 : T.Tm <- P.adup.c(cl, body, (d + 2 : U32), (d + 3 : U32), 42, 0, u0)
        +b2 : T.Tm <- P.adup.c(cl, b1, (d + 3 : U32), (d + 3 : U32), 42, 0, u1)
        P.affine1(cl, nam, "₀", u0)
        P.affine1(cl, nam, "₁", u1)
        return T.tm.lam(lam.ext((d + 1 : U32), U32.is_eq(u0, 0) && U32.is_eq(u1, 0)), T.tm.ddu(lt, T.tm.bjv((d + 1 : U32)), T.tm.lam((d + 2 : U32), T.tm.lam((d + 3 : U32), b2))))

# The term parser
# ===============
#
# hvm.c's parse_term_* functions call each other; Bend has no mutual
# recursion, so they are the cases of one def, pz, and Sel names the
# function (or the point inside one) to run. k is fuel: every call
# inside pz passes its predecessor q. Each case reads as its C original.

type Sel is Data:
  STerm{d: U32}
  SAtom{d: U32}
  SAtomK{k: U32, d: U32}
  SNat{v: U32, d: U32}
  SDry{d: U32}
  SApp{f: T.Tm, d: U32, mp: U32}
  SAppK{k: U32, f: T.Tm, d: U32, mp: U32}
  SArgs{f: T.Tm, d: U32, mp: U32}
  SCtr{nam: U32, d: U32, acc: List<&2, T.Tm>}
  SCtrE{nam: U32, d: U32, acc: List<&2, T.Tm>}
  SLst{d: U32, acc: List<&2, T.Tm>}
  SLstE{d: U32, acc: List<&2, T.Tm>}
  SLam{d: U32}
  SLamB{d: U32}
  SLamU{d: U32}
  SLamA{d: U32}
  SLamS{cl: U32, nam: U32, d: U32}
  SLamI{cl: U32, nam: U32, d: U32}
  SLamID{cl: U32, nam: U32, d: U32}
  SLamIS{cl: U32, nam: U32, d: U32}
  SLamIK{cl: U32, nam: U32, d: U32, dyn: U32, lt: T.Tm, lab: U32}
  SMat{d: U32, acc: List<&2, Cs>}
  SMatK{h: CH, s: List<&2, U32>, d: U32, acc: List<&2, Cs>}
  SMatU{d: U32}
  SMatE{d: U32, acc: List<&2, Cs>}
  SMatD{d: U32, acc: List<&2, Cs>}
  SDup{d: U32}
  SDupK{strict: U32, d: U32}
  SDupEq{strict: U32, cl: U32, nam: U32, d: U32}
  SDupL{strict: U32, cl: U32, nam: U32, d: U32, s: List<&2, U32>}
  SDupUns{nam: U32, nv: U32, d: U32}
  SDupLet{strict: U32, cl: U32, nam: U32, d: U32}
  SDupAmp{cl: U32, nam: U32, d: U32}
  SDupDyn{cl: U32, nam: U32, d: U32}
  SDupSta{cl: U32, nam: U32, d: U32}
  SDPat{d: U32}
  SDPatK{d: U32, s0: List<&2, U32>}
  SDPatKK{k: U32, d: U32, s0: List<&2, U32>}
  SDPatB{dyn: U32, lt: T.Tm, lab: U32, fresh: U32, d: U32}
  SDPatD{lt: T.Tm, n0: NC, n1: NC, v: T.Tm, d: U32}
  SDPatS{lab: U32, n0: NC, n1: NC, v: T.Tm, d: U32}
  SSup{d: U32}
  SSupL{d: U32}
  SSupS{d: U32}
  SSupD{d: U32}
  SSupK{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SSupK2{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SSupR{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SFork{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SSupFork{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SAutoFork{dyn: U32, lt: T.Tm, lab: U32, d: U32}
  SCore{dyn: U32, lt: T.Tm, lab: U32, d: U32, fvs: List<&2, FV>, saved: U32}

def pz(+k: Nat, +sel: Sel) -> P(T.Tm):
  match k:
    case 0n:
      P.die(T.Tm, "out of parser fuel")
    case 1n+q:
      match sel:
        # parse_term
        case STerm{+d}:
          do P<T.Tm>:
            +a : T.Tm <- pz(q, SAtom{d})
            pz(q, SApp{a, d, 0})
        # parse_term_atom
        case SAtom{+d}:
          do P<T.Tm>:
            P.skip()
            +s : List<&2, U32> <- P.src()
            P.setsrc(lx.drop(atom.drop(atom.kind(s)), s))
            pz(q, SAtomK{atom.kind(s), d})
        case SAtomK{+ak, +d}:
          match ak:
            case 1:
              pz(q, SLam{d})
            case 2:
              pz(q, SDup{d})
            case 3:
              pz(q, SSup{d})
            case 4:
              do P<T.Tm>:
                +nam : U32 <- P.name()
                P.skip()
                +b : Bool <- P.try([123])
                P.if(T.Tm, b, P.seq(T.Tm, P.skip(), pz(q, SCtr{nam, d, Nil{}})), P.pure(T.Tm, T.tm.ctr(nam, T.Tn{})))
            case 5:
              do P<T.Tm>:
                +nam : U32 <- P.name()
                return T.tm.ref(nam)
            case 6:
              do P<T.Tm>:
                P.skip()
                +b : Bool <- P.at(40)
                P.if(T.Tm, b, pz(q, SDry{d}), P.bind(U32, T.Tm, P.name_num(), n => P.pure(T.Tm, T.tm.nam(n))))
            case 7:
              do P<T.Tm>:
                +x : T.Tm <- pz(q, SAtom{d})
                return T.tm.inc(x)
            case 8:
              P.pure(T.Tm, T.tm.any())
            case 9:
              do P<T.Tm>:
                +t : T.Tm <- pz(q, STerm{d})
                P.consume([41], ")")
                return t
            case 10:
              do P<T.Tm>:
                P.adv()
                P.skip()
                +b : Bool <- P.at(93)
                P.if(T.Tm, b, P.seq(T.Tm, P.adv(), P.pure(T.Tm, nil())), pz(q, SLst{d, Nil{}}))
            case 11:
              do P<T.Tm>:
                +c : U32 <- P.charlit()
                return chr(c)
            case 12:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                P.str.go(lx.sl(4294967295n, lx.hd(s), Nil{}, SLAt{lx.tl(s), U32.is_eq(lx.hd(lx.tl(s)), lx.hd(s))}))
            case 13:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                +ds : List<&2, U32> = lx.digits(s)
                +r : List<&2, U32> = lx.drop(lx.len(ds), s)
                +v : U32 = lx.dec(ds, 0)
                P.if(T.Tm, is.c(r, 110), P.seq(T.Tm, P.setsrc(lx.tl(r)), pz(q, SNat{v, d})), P.seq(T.Tm, P.setsrc(r), P.seq(T.Tm, P.skip(), P.pure(T.Tm, T.tm.num(v)))))
            case x:
              do P<T.Tm>:
                P.skip()
                +nam : U32 <- P.name()
                P.skip()
                +b0 : Bool <- P.try(L.s0())
                +b1 : Bool <- P.try.if(b0, L.s1())
                P.skip()
                +bs : List<&2, PB> <- P.binds()
                +fs : U32 <- P.fside()
                +side : U32 = u.pick(b0, 0, u.pick(b1, 1, 2))
                P.var.go(bd.look(bs, nam, side, 0), nam, side, fs)
        # parse_term_nat, after `Nn`
        case SNat{+v, +d}:
          do P<T.Tm>:
            +b : Bool <- P.try([43])
            +t : T.Tm <- P.if(T.Tm, b, pz(q, STerm{d}), P.pure(T.Tm, T.Tl{13, 0, 0}))
            return nat.wrap(U32.to_nat(v), t)
        # parse_term_nam: ^(f x)
        case SDry{+d}:
          do P<T.Tm>:
            P.consume([40], "(")
            +f : T.Tm <- pz(q, STerm{d})
            +x : T.Tm <- pz(q, STerm{d})
            P.consume([41], ")")
            return T.tm.two(10, 0, f, x)
        # parse_term_app_prec
        case SApp{+f, +d, +mp}:
          do P<T.Tm>:
            P.skip()
            +s : List<&2, U32> <- P.src()
            pz(q, SAppK{app.kind(s, mp), f, d, mp})
        case SAppK{+ak, +f, +d, +mp}:
          match ak:
            case 1:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                P.setsrc(lx.drop(2n, s))
                +t : T.Tm <- pz(q, STerm{d})
                pz(q, SApp{con(f, t), d, mp})
            case 2:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                P.setsrc(lx.drop(3n, s))
                +r : T.Tm <- pz(q, SAtom{d})
                +r2 : T.Tm <- pz(q, SApp{r, d, 4})
                pz(q, SApp{T.tm.two(36, 0, f, r2), d, mp})
            case 3:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                P.setsrc(lx.drop(3n, s))
                +r : T.Tm <- pz(q, SAtom{d})
                +r2 : T.Tm <- pz(q, SApp{r, d, 2})
                pz(q, SApp{T.tm.two(37, 0, f, r2), d, mp})
            case 4:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                P.setsrc(lx.drop(3n, s))
                +r : T.Tm <- pz(q, SAtom{d})
                +r2 : T.Tm <- pz(q, SApp{r, d, 1})
                pz(q, SApp{T.tm.two(38, 0, f, r2), d, mp})
            case 5:
              do P<T.Tm>:
                +s : List<&2, U32> <- P.src()
                +op : U32 = opr.peek(s)
                P.setsrc(lx.drop(opr.len(op), s))
                +r : T.Tm <- pz(q, SAtom{d})
                +r2 : T.Tm <- pz(q, SApp{r, d, (opr.prec(op) + 1 : U32)})
                pz(q, SApp{T.tm.op2(op, f, r2), d, mp})
            case 6:
              do P<T.Tm>:
                P.consume([40], "(")
                +b : Bool <- P.at(41)
                P.if(T.Tm, b, P.seq(T.Tm, P.consume([41], ")"), pz(q, SApp{f, d, mp})), pz(q, SArgs{f, d, mp}))
            case x:
              P.pure(T.Tm, f)
        case SArgs{+f, +d, +mp}:
          do P<T.Tm>:
            +a : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            +b : Bool <- P.at(41)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([41], ")"), pz(q, SApp{T.tm.app(f, a), d, mp})), pz(q, SArgs{T.tm.app(f, a), d, mp}))
        # parse_term_ctr's fields
        case SCtr{+nam, +d, +acc}:
          do P<T.Tm>:
            +b : Bool <- P.at(125)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([125], "}"), P.pure(T.Tm, T.tm.ctr(nam, kids.of(acc, T.Tn{})))), pz(q, SCtrE{nam, d, acc}))
        case SCtrE{+nam, +d, +acc}:
          do P<T.Tm>:
            +x : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            pz(q, SCtr{nam, d, x <> acc})
        # parse_term_lst's elements
        case SLst{+d, +acc}:
          do P<T.Tm>:
            +b : Bool <- P.at(93)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([93], "]"), P.pure(T.Tm, lst.build(acc, nil()))), pz(q, SLstE{d, acc}))
        case SLstE{+d, +acc}:
          do P<T.Tm>:
            +x : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            pz(q, SLst{d, x <> acc})
        # parse_term_lam (after λ)
        case SLam{+d}:
          do P<T.Tm>:
            P.skip()
            +s : List<&2, U32> <- P.src()
            P.if(T.Tm, is.c(s, 123), pz(q, SLamB{d}), P.if(T.Tm, is.c(s, 36), P.seq(T.Tm, P.adv(), pz(q, SLamU{d})), pz(q, SLamA{d})))
        case SLamB{+d}:
          do P<T.Tm>:
            P.consume([123], "{")
            P.skip()
            +b : Bool <- P.at(125)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([125], "}"), P.pure(T.Tm, T.tm.era())), pz(q, SMat{d, Nil{}}))
        # λ$x. body
        case SLamU{+d}:
          do P<T.Tm>:
            +nam : U32 <- P.name()
            P.skip()
            P.push(pb(nam, (d + 1 : U32), 0, 0, 0))
            +b : Bool <- P.sep()
            +body : T.Tm <- P.if(T.Tm, b, pz(q, SLam{(d + 2 : U32)}), P.seq(T.Tm, P.consume([46], "."), pz(q, STerm{(d + 2 : U32)})))
            P.pop(1n)
            +uses : U32 = T.tm.uses(body, (d + 2 : U32), 42, 0)
            P.affine(U32.is_gt(uses, 1), nam, "", uses)
            return T.tm.uns(T.tm.lam((d + 1 : U32), T.tm.lam(lam.ext((d + 2 : U32), U32.is_eq(uses, 0)), T.tm.app(T.tm.bjv((d + 1 : U32)), body))))
        case SLamA{+d}:
          do P<T.Tm>:
            +cl : Bool <- P.try([38])
            +nam : U32 <- P.name()
            P.skip()
            +b : Bool <- P.at(38)
            P.if(T.Tm, b, P.seq(T.Tm, P.adv(), pz(q, SLamI{u.b2u(cl), nam, d})), pz(q, SLamS{u.b2u(cl), nam, d}))
        # λx. body (and λ&x, λx,y)
        case SLamS{+cl, +nam, +d}:
          do P<T.Tm>:
            P.push(pb(nam, d, 0, 0, cl))
            +b : Bool <- P.sep()
            +body : T.Tm <- P.if(T.Tm, b, pz(q, SLam{(d + 1 : U32)}), P.seq(T.Tm, P.consume([46], "."), pz(q, STerm{(d + 1 : U32)})))
            P.pop(1n)
            +uses : U32 = T.tm.uses(body, (d + 1 : U32), 42, 0)
            +b2 : T.Tm <- P.adup.c(cl, body, (d + 1 : U32), (d + 1 : U32), 42, 0, uses)
            P.affine1(cl, nam, "", uses)
            return T.tm.lam(lam.ext((d + 1 : U32), U32.is_eq(uses, 0)), b2)
        # λx&L / λx& / λx&(L) (after the &)
        case SLamI{+cl, +nam, +d}:
          do P<T.Tm>:
            P.skip()
            +b : Bool <- P.at(40)
            P.if(T.Tm, b, pz(q, SLamID{cl, nam, d}), pz(q, SLamIS{cl, nam, d}))
        case SLamID{+cl, +nam, +d}:
          do P<T.Tm>:
            P.consume([40], "(")
            +lt : T.Tm <- pz(q, STerm{(d + 1 : U32)})
            P.consume([41], ")")
            P.skip()
            pz(q, SLamIK{cl, nam, d, 1, lt, 0})
        case SLamIS{+cl, +nam, +d}:
          do P<T.Tm>:
            +s : List<&2, U32> <- P.src()
            +lab : U32 <- P.if(U32, is.c(s, 44) || is.c(s, 59) || is.c(s, 46), P.fresh(), P.name_num())
            P.skip()
            pz(q, SLamIK{cl, nam, d, 0, dummy(), lab})
        case SLamIK{+cl, +nam, +d, +dyn, +lt, +lab}:
          do P<T.Tm>:
            +dd : U32 = u.pick(U32.is_ne(dyn, 0), 3, 2)
            P.push(pb(nam, (d + 1 : U32), u.pick(U32.is_ne(dyn, 0), 16777215, lab), 0, cl))
            +b : Bool <- P.sep()
            +body : T.Tm <- P.if(T.Tm, b, pz(q, SLam{(d + dd : U32)}), P.seq(T.Tm, P.consume([46], "."), pz(q, STerm{(d + dd : U32)})))
            P.pop(1n)
            P.lami.fin(cl, nam, d, dyn, lt, lab, body)
        # λ{ ... } cases; acc newest first
        case SMat{+d, +acc}:
          do P<T.Tm>:
            P.skip()
            +s : List<&2, U32> <- P.src()
            +h : CH <- P.case(s)
            pz(q, SMatK{h, s, d, acc})
        case SMatK{+h, +s, +d, +acc}:
          match h:
            case CHYes{+tag, +ext}:
              do P<T.Tm>:
                P.skip()
                P.consume([58], ":")
                +v : T.Tm <- pz(q, STerm{d})
                P.skip()
                P.sepu()
                pz(q, SMat{d, Cs{tag, ext, v} <> acc})
            case CHNo{}:
              P.seq(T.Tm, P.setsrc(s), P.if(T.Tm, lst.is_nil(acc), pz(q, SMatU{d}), pz(q, SMatE{d, acc})))
        case SMatU{+d}:
          do P<T.Tm>:
            +f : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            P.consume([125], "}")
            return T.tm.use(f)
        case SMatE{+d, +acc}:
          do P<T.Tm>:
            +b : Bool <- P.at(125)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([125], "}"), P.pure(T.Tm, mat.chain(acc, T.tm.num(0)))), pz(q, SMatD{d, acc}))
        case SMatD{+d, +acc}:
          do P<T.Tm>:
            +b : Bool <- P.at(95)
            P.if(Unit, b, P.seq(Unit, P.adv(), P.seq(Unit, P.skip(), P.consume([58], ":"))), P.unit())
            +t : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            P.consume([125], "}")
            return mat.chain(acc, t)
        # parse_term_dup (after !)
        case SDup{+d}:
          do P<T.Tm>:
            P.skip()
            +st : Bool <- P.try([33])
            P.skip()
            +pat : T.Tm <- pz(q, SDPat{d})
            P.if(T.Tm, is.sent(pat), pz(q, SDupK{u.b2u(st), d}), P.pure(T.Tm, pat))
        case SDupK{+strict, +d}:
          do P<T.Tm>:
            +cl : U32 <- P.tamp()
            +nam : U32 <- P.name()
            P.skip()
            +b : Bool <- P.at(61)
            P.if(T.Tm, b, P.seq(T.Tm, P.adv(), P.seq(T.Tm, P.skip(), pz(q, SDupEq{strict, cl, nam, d}))), P.seq(T.Tm, P.consume([38], "&"), P.seq(T.Tm, P.skip(), pz(q, SDupAmp{cl, nam, d}))))
        case SDupEq{+strict, +cl, +nam, +d}:
          do P<T.Tm>:
            +s : List<&2, U32> <- P.src()
            +b : Bool <- P.try(L.lam())
            P.if(T.Tm, b, pz(q, SDupL{strict, cl, nam, d, s}), pz(q, SDupLet{strict, cl, nam, d}))
        case SDupL{+strict, +cl, +nam, +d, +s}:
          do P<T.Tm>:
            P.skip()
            +nv : U32 <- P.name()
            P.skip()
            +b : Bool <- P.try([59])
            P.if(T.Tm, b, P.seq(T.Tm, P.skip(), pz(q, SDupUns{nam, nv, d})), P.seq(T.Tm, P.setsrc(s), pz(q, SDupLet{strict, cl, nam, d})))
        # ! f = λ x ; body
        case SDupUns{+nam, +nv, +d}:
          do P<T.Tm>:
            P.push(pb(nam, d, 0, 0, 0))
            P.push(pb(nv, (d + 1 : U32), 0, 0, 0))
            +body : T.Tm <- pz(q, STerm{(d + 2 : U32)})
            P.pop(2n)
            +uf : U32 = T.tm.uses(body, (d + 1 : U32), 42, 0)
            +uv : U32 = T.tm.uses(body, (d + 2 : U32), 42, 0)
            P.affine(U32.is_gt(uf, 1), nam, "", uf)
            P.affine(U32.is_gt(uv, 1), nv, "", uv)
            return T.tm.uns(T.tm.lam((d + 1 : U32), T.tm.lam((d + 2 : U32), body)))
        # ! x = v; body  (and !!x, !&x)
        case SDupLet{+strict, +cl, +nam, +d}:
          do P<T.Tm>:
            +v : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.push(pb(nam, d, 0, 0, cl))
            +body : T.Tm <- pz(q, STerm{(d + 1 : U32)})
            P.pop(1n)
            +uses : U32 = T.tm.uses(body, (d + 1 : U32), 42, 0)
            +b2 : T.Tm <- P.adup.c(cl, body, (d + 1 : U32), (d + 1 : U32), 42, 0, uses)
            P.affine1(cl, nam, "", uses)
            return T.tm.app(let.lam(strict, T.tm.lam((d + 1 : U32), b2)), v)
        case SDupAmp{+cl, +nam, +d}:
          do P<T.Tm>:
            +b : Bool <- P.at(40)
            P.if(T.Tm, b, pz(q, SDupDyn{cl, nam, d}), pz(q, SDupSta{cl, nam, d}))
        # ! x &(lab) = v; body
        case SDupDyn{+cl, +nam, +d}:
          do P<T.Tm>:
            P.consume([40], "(")
            +lt : T.Tm <- pz(q, STerm{d})
            P.consume([41], ")")
            P.consume([61], "=")
            +v : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            P.push(pb(nam, d, 16777215, 0, cl))
            +body : T.Tm <- pz(q, STerm{(d + 2 : U32)})
            P.pop(1n)
            +u0 : U32 = T.tm.uses(body, (d + 1 : U32), 42, 0)
            +u1 : U32 = T.tm.uses(body, (d + 2 : U32), 42, 0)
            +b1 : T.Tm <- P.adup.c(cl, body, (d + 1 : U32), (d + 2 : U32), 42, 0, u0)
            +b2 : T.Tm <- P.adup.c(cl, b1, (d + 2 : U32), (d + 2 : U32), 42, 0, u1)
            P.affine1(cl, nam, "₀", u0)
            P.affine1(cl, nam, "₁", u1)
            return T.tm.ddu(lt, v, T.tm.lam((d + 1 : U32), T.tm.lam((d + 2 : U32), b2)))
        # ! x &L = v; body  (and ! x & = v; body)
        case SDupSta{+cl, +nam, +d}:
          do P<T.Tm>:
            +b : Bool <- P.at(61)
            +lab : U32 <- P.if(U32, b, P.fresh(), P.name_num())
            P.consume([61], "=")
            +v : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            P.push(pb(nam, d, lab, 0, cl))
            +body : T.Tm <- pz(q, STerm{(d + 1 : U32)})
            P.pop(1n)
            +u0 : U32 = T.tm.uses(body, (d + 1 : U32), 43, lab)
            +u1 : U32 = T.tm.uses(body, (d + 1 : U32), 44, lab)
            +b1 : T.Tm <- P.adup.c(cl, body, (d + 1 : U32), (d + 1 : U32), 44, lab, u1)
            +b2 : T.Tm <- P.adup.c(cl, b1, (d + 1 : U32), (d + 1 : U32), 43, lab, u0)
            P.affine1(cl, nam, "₀", u0)
            P.affine1(cl, nam, "₁", u1)
            return T.tm.dup(lab, v, b2)
        # parse_term_dup_pat: ! &L{x,y} = v; body; the sentinel if none
        case SDPat{+d}:
          do P<T.Tm>:
            +s0 : List<&2, U32> <- P.src()
            P.skip()
            +b : Bool <- P.try([38])
            P.if(T.Tm, b, P.seq(T.Tm, P.skip(), pz(q, SDPatK{d, s0})), P.pure(T.Tm, sent()))
        case SDPatK{+d, +s0}:
          do P<T.Tm>:
            +s : List<&2, U32> <- P.src()
            pz(q, SDPatKK{dup.patk.go(s), d, s0})
        case SDPatKK{+pk, +d, +s0}:
          match pk:
            case 1:
              do P<T.Tm>:
                P.consume([40], "(")
                +lt : T.Tm <- pz(q, STerm{d})
                P.consume([41], ")")
                P.skip()
                +b : Bool <- P.at(123)
                P.need(b, "{")
                pz(q, SDPatB{1, lt, 0, 0, d})
            case 2:
              pz(q, SDPatB{0, dummy(), 0, 1, d})
            case 3:
              do P<T.Tm>:
                +lab : U32 <- P.name_num()
                pz(q, SDPatB{0, dummy(), lab, 0, d})
            case x:
              P.seq(T.Tm, P.setsrc(s0), P.pure(T.Tm, sent()))
        case SDPatB{+dyn, +lt, +lab0, +fresh, +d}:
          do P<T.Tm>:
            P.consume([123], "{")
            +n0 : NC <- P.patname()
            P.skip()
            P.sepu()
            +n1 : NC <- P.patname()
            P.skip()
            P.sepu()
            P.consume([125], "}")
            P.need(U32.is_ne(pr.fst(n0), pr.fst(n1)), "distinct names in dup pattern")
            +lab : U32 <- P.if(U32, U32.is_ne(fresh, 0), P.fresh(), P.pure(U32, lab0))
            P.consume([61], "=")
            +v : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.skip()
            P.if(T.Tm, U32.is_ne(dyn, 0), pz(q, SDPatD{lt, n0, n1, v, d}), pz(q, SDPatS{lab, n0, n1, v, d}))
        case SDPatD{+lt, +n0, +n1, +v, +d}:
          do P<T.Tm>:
            P.push(pb.side(pr.fst(n0), d, 16777215, 0, pr.snd(n0)))
            P.push(pb.side(pr.fst(n1), d, 16777215, 1, pr.snd(n1)))
            +body : T.Tm <- pz(q, STerm{(d + 2 : U32)})
            P.pop(2n)
            +u0 : U32 = T.tm.uses(body, (d + 1 : U32), 42, 0)
            +u1 : U32 = T.tm.uses(body, (d + 2 : U32), 42, 0)
            +b1 : T.Tm <- P.adup.c(pr.snd(n0), body, (d + 1 : U32), (d + 2 : U32), 42, 0, u0)
            +b2 : T.Tm <- P.adup.c(pr.snd(n1), b1, (d + 2 : U32), (d + 2 : U32), 42, 0, u1)
            P.affine1(pr.snd(n0), pr.fst(n0), "", u0)
            P.affine1(pr.snd(n1), pr.fst(n1), "", u1)
            return T.tm.ddu(lt, v, T.tm.lam((d + 1 : U32), T.tm.lam((d + 2 : U32), b2)))
        case SDPatS{+lab, +n0, +n1, +v, +d}:
          do P<T.Tm>:
            P.push(pb.side(pr.fst(n0), d, lab, 0, pr.snd(n0)))
            P.push(pb.side(pr.fst(n1), d, lab, 1, pr.snd(n1)))
            +body : T.Tm <- pz(q, STerm{(d + 1 : U32)})
            P.pop(2n)
            +u0 : U32 = T.tm.uses(body, (d + 1 : U32), 43, lab)
            +u1 : U32 = T.tm.uses(body, (d + 1 : U32), 44, lab)
            +b1 : T.Tm <- P.adup.c(pr.snd(n1), body, (d + 1 : U32), (d + 1 : U32), 44, lab, u1)
            +b2 : T.Tm <- P.adup.c(pr.snd(n0), b1, (d + 1 : U32), (d + 1 : U32), 43, lab, u0)
            P.affine1(pr.snd(n0), pr.fst(n0), "", u0)
            P.affine1(pr.snd(n1), pr.fst(n1), "", u1)
            return T.tm.dup(lab, v, b2)
        # parse_term_sup (after &)
        case SSup{+d}:
          do P<T.Tm>:
            P.skip()
            +b : Bool <- P.at(123)
            P.if(T.Tm, b, P.seq(T.Tm, P.consume([123], "{"), P.seq(T.Tm, P.consume([125], "}"), P.pure(T.Tm, T.tm.era()))), pz(q, SSupL{d}))
        case SSupL{+d}:
          do P<T.Tm>:
            +b : Bool <- P.at(40)
            P.if(T.Tm, b, pz(q, SSupD{d}), pz(q, SSupS{d}))
        case SSupS{+d}:
          do P<T.Tm>:
            +lab : U32 <- P.name_num()
            pz(q, SSupK{0, dummy(), lab, d})
        case SSupD{+d}:
          do P<T.Tm>:
            P.consume([40], "(")
            +lt : T.Tm <- pz(q, STerm{d})
            P.consume([41], ")")
            pz(q, SSupK{1, lt, 0, d})
        case SSupK{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            P.skip()
            +b : Bool <- P.try(L.lam())
            P.if(T.Tm, b, pz(q, SFork{dyn, lt, lab, d}), pz(q, SSupK2{dyn, lt, lab, d}))
        case SSupK2{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            +s : List<&2, U32> <- P.src()
            P.if(T.Tm, is.c(s, 33) && U32.is_eq(lx.at(1n, s), 123), P.seq(T.Tm, P.consume([33], "!"), pz(q, SAutoFork{dyn, lt, lab, d})), P.if(T.Tm, is.c(s, 91), P.seq(T.Tm, P.consume([91], "["), pz(q, SSupFork{dyn, lt, lab, d})), pz(q, SSupR{dyn, lt, lab, d})))
        case SSupR{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            P.consume([123], "{")
            +t0 : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            +t1 : T.Tm <- pz(q, STerm{d})
            P.skip()
            P.sepu()
            P.consume([125], "}")
            return sup.mk(dyn, lt, lab, t0, t1)
        # parse_term_fork: &Lλx,y{A;B}
        case SFork{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            +fs0 : U32 <- P.fside()
            +n0 : U32 <- P.name()
            P.skip()
            +names : List<&2, U32> <- P.fnames(4294967295n, Some{n0}, Nil{})
            P.consume([123], "{")
            +dd : U32 = u.pick(U32.is_ne(dyn, 0), 3, 2)
            P.pushes(fork.binds(names, 0, d, dd, u.pick(U32.is_ne(dyn, 0), 16777215, lab)))
            +n : U32 = u.len(U32, names)
            +bd : U32 = (d + n * dd : U32)
            P.optside(L.amp0())
            P.setside(0)
            +left : T.Tm <- pz(q, STerm{bd})
            P.skip()
            P.sepu()
            P.skip()
            P.optside(L.amp1())
            P.setside(1)
            +right : T.Tm <- pz(q, STerm{bd})
            P.setside(fs0)
            P.skip()
            P.sepu()
            P.consume([125], "}")
            P.pop(U32.to_nat(n))
            P.forkchk(names, 0, d, dd, dyn, lab, left, right)
            return fork.wrap(U32.to_nat(n), (n - 1 : U32), d, dd, dyn, lt, lab, sup.mk(dyn, lt, lab, left, right))
        # parse_term_sup_fork: &L[x,&y]{A;B}
        case SSupFork{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            +fs0 : U32 <- P.fside()
            P.skip()
            +fvs : List<&2, FV> <- P.bind(Maybe<&2, FV>, List<&2, FV>, P.sfv.step(fs0), r => P.sfvs(4294967295n, fs0, r, Nil{}))
            P.consume([93], "]")
            P.skip()
            P.consume([123], "{")
            P.skip()
            pz(q, SCore{dyn, lt, lab, d, fvs, fs0})
        # parse_term_auto_fork: &L!{A;B}
        case SAutoFork{+dyn, +lt, +lab, +d}:
          do P<T.Tm>:
            +fs0 : U32 <- P.fside()
            +bs : List<&2, PB> <- P.binds()
            P.consume([123], "{")
            P.skip()
            pz(q, SCore{dyn, lt, lab, d, af.collect(List.reverse(&2, PB, bs), Nil{}, fs0), fs0})
        # parse_term_sup_fork_core
        case SCore{+dyn, +lt, +lab, +d, +fvs, +saved}:
          do P<T.Tm>:
            P.setside(2)
            +dd : U32 = u.pick(U32.is_ne(dyn, 0), 2, 1)
            P.pushes(fc.binds(fvs, 0, d, dd, u.pick(U32.is_ne(dyn, 0), 16777215, lab)))
            +n : U32 = u.len(FV, fvs)
            +bd : U32 = (d + n * dd : U32)
            P.optside(L.amp0())
            P.setside(0)
            +left : T.Tm <- pz(q, STerm{bd})
            P.skip()
            P.sepu()
            P.skip()
            P.optside(L.amp1())
            P.setside(1)
            +right : T.Tm <- pz(q, STerm{bd})
            P.setside(saved)
            P.skip()
            P.sepu()
            P.consume([125], "}")
            P.pop(U32.to_nat(n))
            +lr : LR <- P.fcpost(fvs, 0, d, dd, dyn, lab, bd, left, right)
            return fc.wrap(List.reverse(&2, FV, fvs), (n - 1 : U32), d, dd, dyn, lt, lab, sup.mk(dyn, lt, lab, lr.l(lr), lr.r(lr)))

# Definitions
# ===========

# what parse_def stops at: the end, or an #include (its file name)
type DR is Data:
  DDone{}
  DInc{name: List<&2, U32>}

def P.include() -> P(DR):
  do P<DR>:
    P.consume([34], "\"")
    +s : List<&2, U32> <- P.src()
    P.setsrc(lx.drop(lx.len(lx.until(s)), s))
    P.consume([34], "\"")
    return DInc{lx.until(s)}

# one `@name = term`
def P.def1() -> P(Unit):
  do P<Unit>:
    P.adv()
    +id : U32 <- P.name()
    P.consume([61], "=")
    P.clear()
    +t : T.Tm <- pz(4294967295n, STerm{0})
    P.adddef(id, t)

# parse_def: definitions up to the end or the next #include
def P.defs(k: Nat) -> P(DR):
  match k:
    case 0n:
      P.die(DR, "out of fuel: too many definitions")
    case 1n+q:
      do P<DR>:
        P.skip()
        +s : List<&2, U32> <- P.src()
        P.if(DR, lx.is_end(s), P.pure(DR, DDone{}), P.if(DR, lx.starts(L.include(), s), P.seq(DR, P.setsrc(lx.drop(8n, s)), P.include()), P.if(DR, is.c(s, 64), P.seq(DR, P.def1(), P.defs(q)), P.fail(DR, "definition or #include"))))
