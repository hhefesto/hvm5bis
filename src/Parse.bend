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
  PEr{e: String}

def P(-X: Type) -> Type:
  St -> PR<X>

def P.pure(-X: Type, x: X) -> P(X):
  st => POk{st, x}

def P.go(-X: Type, -Y: Type, r: PR<X>, f: X -> P(Y)) -> PR<Y>:
  match r:
    case POk{st, x}:
      f(x, st)
    case PEr{e}:
      PEr{e}

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
  st => PEr{msg}

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
  String.from_list([Chr{27}, Chr{91}, Chr{49}, Chr{59}, Chr{51}, Chr{49}, Chr{109}]) ++ "PARSE_ERROR" ++ String.from_list([Chr{27}, Chr{91}, Chr{48}, Chr{109}])

# parse_error: expected `what`, detected the next byte
def P.fail(-X: Type, what: String) -> P(X):
  +st => PEr{P.red() ++ "\n- expected: " ++ what ++ "\n- detected: " ++ lx.detected(st.src(st))}

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

def P.name_num.chk.go(z: Bool, +cs: List<&2, U32>) -> P(Unit):
  match z:
    case True{}:
      P.die(Unit, P.red() ++ "\n- base64 name '" ++ lx.str(cs) ++ "' exceeds 24-bit limit (max 0xFFFFFF)")
    case False{}:
      P.unit()

def P.name_num.chk(+cs: List<&2, U32>) -> P(Unit):
  P.name_num.chk.go(Nat.is_gt(lx.len(cs), 4n), cs)
# parse_name_num: a nick name as a 24-bit number (labels, ^names)
def P.name_num() -> P(U32):
  do P<U32>:
    P.skip()
    +s : List<&2, U32> <- P.src()
    P.need(lx.is_init(lx.hd(s)), "name")
    P.name_num.chk(lx.name(s))
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
