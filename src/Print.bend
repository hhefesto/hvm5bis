import Base
import ./Wnf.bend as W

# hvm5bis: the printer, a port of the Print section of HVM4's src/hvm.c.
#
# Meaning. print_term writes a dynamic (linked) term: a lambda is named
# by its body's heap location, in order of first sight (a, b, .., z, aa,
# ..); a dup node by its expr location (A, B, ..), and every dup node met
# is printed after the term as `;!A&L=value;`. A variable whose cell holds
# a substitution prints the substituted term. print_term_quoted writes a
# quoted term (BJV/BJ0/BJ1 de Bruijn levels, as the collapser makes),
# naming binders by depth. ALO terms print their book term under their
# bind list.
#
# Shape. hvm.c's printer is mutually recursive (print_term_go, print_app,
# print_ctr); here it is one def, pr, over print steps (PSel): a step
# prints a word, the word at a location, some text, or a list of steps
# in order. The state threads the heap (reads hand it back), the naming
# tables (PN), the mode (PM) and the output (code points, newest first).

type Wd is Data:
  Wd{hi: U32, lo: U32}

type LB is Data:
  LB{loc: U32, name: U32}

type DB is Data:
  DB{loc: U32, name: U32, lab: U32}

# naming: lambdas and dups seen (newest first) and how many; dprint:
# how many dups print_term_finish has printed
type PN is Data:
  PN{lams: List<&2, LB>, nlam: U32, dups: List<&2, DB>, ndup: U32, dprint: U32}

# mode: quoted (0/1), the ALO bind list and its length
type PM is Data:
  PM{quoted: U32, subst: U32, slen: U32}

# the name table (newest first) and its size
type Env is Data:
  Env{names: List<&2, String>, ntab: U32}

type PSel is Data:
  PT{hi: U32, lo: U32, d: U32}
  PTg{t: U32, hi: U32, lo: U32, d: U32}
  PAt{loc: U32, d: U32}
  PE{cs: List<&2, U32>}
  PL{xs: List<&2, PSel>}
  PMode{qt: U32, sub: U32, len: U32, hi: U32, lo: U32, d: U32}
  PRest{m: PM}
  PLam{loc: U32}
  PDupN{loc: U32, lab: U32}
  PDupReg{loc: U32, lab: U32}
  PVar{loc: U32, d: U32}
  PDp{t: U32, loc: U32, lab: U32, d: U32}
  PBj{t: U32, lvl: U32, lab: U32, d: U32}
  PApp{hi: U32, lo: U32, d: U32}
  PMat{hi: U32, lo: U32, d: U32}
  PMatN{hi: U32, lo: U32, d: U32}
  PCtr{hi: U32, lo: U32, d: U32}
  PArgs{xs: List<&2, Wd>, d: U32, first: Bool}
  PAlo{hi: U32, lo: U32}
  PUns{lo: U32, d: U32}
  PFin{first: Bool}
  PRun{}

# Text
# ====

def PW() -> Type:
  Array<U32> & PN & PM & List<&2, U32> & PSel

def u.pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def tx.rev(cs: List<&2, Char>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      tx.rev(t, Char.to_u32(c) <> acc)

# a String's code points
def tx(s: String) -> List<&2, U32>:
  List.reverse(&2, U32, tx.rev(String.to_list(s), Nil{}))

def tx.num(+n: U32) -> List<&2, U32>:
  tx(U32.show(n))

def rev.onto(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      rev.onto(t, c <> acc)

# nick_alphabet
def nick.chr(+n: U32) -> U32:
  u.pick(U32.is_eq(n, 0), 95, u.pick(U32.is_le(n, 26), (n + 96 : U32), u.pick(U32.is_le(n, 52), (n + 38 : U32), u.pick(U32.is_le(n, 62), (n - 5 : U32), 36))))

def pname.go(k: Nat, z: Bool, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k z:
    case 0n _:
      acc
    case _ True{}:
      nick.chr(n) <> acc
    case 1n+q False{}:
      pname.go(q, U32.is_lt(U32.div(n, 64), 64), U32.div(n, 64), nick.chr(U32.mod(n, 64)) <> acc)

# print_name: a number in the nick alphabet
def pname(+n: U32) -> List<&2, U32>:
  pname.go(8n, U32.is_lt(n, 64), n, Nil{})

def alpha.go(k: Nat, z: Bool, +n: U32, +base: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k z:
    case 0n _:
      acc
    case _ True{}:
      acc
    case 1n+q False{}:
      alpha.go(q, U32.is_eq(U32.div((n - 1 : U32), 26), 0), U32.div((n - 1 : U32), 26), base, (base + U32.mod((n - 1 : U32), 26) : U32) <> acc)

def alpha.z(z: Bool, +n: U32, +base: U32) -> List<&2, U32>:
  match z:
    case True{}:
      [95]
    case False{}:
      alpha.go(8n, False{}, n, base, Nil{})

def alpha(+n: U32, +base: U32) -> List<&2, U32>:
  alpha.z(U32.is_eq(n, 0), n, base)

def name.of.k(r: Maybe<&2, String>, +id: U32) -> List<&2, U32>:
  match r:
    case None{}:
      pname(id)
    case Some{s}:
      tx(s)

def name.of.ids(z: Bool, names: List<&2, String>, +ntab: U32, +id: U32) -> List<&2, U32>:
  match z:
    case True{}:
      name.of.k(List.get(&2, String, names, U32.to_nat((ntab - 1 - id : U32))), id)
    case False{}:
      pname(id)

# table_get, or the nick fallback
def name.of(+env: Env, +id: U32) -> List<&2, U32>:
  match env:
    case Env{names, +ntab}:
      name.of.ids(U32.is_lt(id, ntab), names, ntab, id)

# print_mat_name
def mat.name(+env: Env, +nam: U32) -> List<&2, U32>:
  match nam:
    case 0:
      [48, 110]
    case 1:
      [49, 110, 43]
    case 2:
      [91, 93]
    case 3:
      [60, 62]
    case x:
      35 <> name.of(env, x)

def op.sym(+o: U32) -> List<&2, U32>:
  match o:
    case 0:
      [43]
    case 1:
      [45]
    case 2:
      [42]
    case 3:
      [47]
    case 4:
      [37]
    case 5:
      [38, 38]
    case 6:
      [124, 124]
    case 7:
      [94]
    case 8:
      [60, 60]
    case 9:
      [62, 62]
    case 10:
      [126]
    case 11:
      [61, 61]
    case 12:
      [33, 61]
    case 13:
      [60]
    case 14:
      [60, 61]
    case 15:
      [62]
    case 16:
      [62, 61]
    case x:
      63 <> tx.num(x)

def can.esc.rest(+c: U32) -> Bool:
  U32.is_le(c, 1114111) && Bool.not(U32.is_le(55296, c) && U32.is_le(c, 57343)) && U32.is_ge(c, 32) && U32.is_ne(c, 127) && Bool.not(U32.is_le(128, c) && U32.is_le(c, 159))

# print_utf8_can_escape (mode 0 a char, 1 a string)
def can.esc(+c: U32, +mode: U32) -> Bool:
  match c:
    case 10:
      True{}
    case 9:
      True{}
    case 13:
      True{}
    case 0:
      True{}
    case 92:
      True{}
    case 39:
      U32.is_eq(mode, 0) || can.esc.rest(c)
    case 34:
      U32.is_eq(mode, 1) || can.esc.rest(c)
    case x:
      can.esc.rest(x)

def esc.q(z: Bool, +c: U32) -> List<&2, U32>:
  match z:
    case True{}:
      [92, c]
    case False{}:
      [c]

# Naming
# ======

def esc(+c: U32, +mode: U32) -> List<&2, U32>:
  match c:
    case 10:
      [92, 110]
    case 9:
      [92, 116]
    case 13:
      [92, 114]
    case 0:
      [92, 48]
    case 92:
      [92, 92]
    case 39:
      esc.q(U32.is_eq(mode, 0), 39)
    case 34:
      esc.q(U32.is_eq(mode, 1), 34)
    case x:
      [x]

def st.lam.new(z: Bool, +f: U32, +loc: U32, lams: List<&2, LB>, +nlam: U32, dups: List<&2, DB>, +ndup: U32, +dp: U32) -> PN & U32:
  match z:
    case True{}:
      (PN{LB{loc, (nlam + 1 : U32)} <> lams, (nlam + 1 : U32), dups, ndup, dp}, (nlam + 1 : U32))
    case False{}:
      (PN{lams, nlam, dups, ndup, dp}, f)

# alo_subst_get: the idx-th bind node (0 = innermost); z: ls is 0
def st.lam.k(+f: U32, +loc: U32, pn: PN) -> PN & U32:
  match pn:
    case PN{lams, +nlam, dups, ndup, dp}:
      st.lam.new(U32.is_eq(f, 0), f, loc, lams, nlam, dups, ndup, dp)

def st.dup.new(z: Bool, +f: U32, +loc: U32, +lab: U32, lams: List<&2, LB>, +nlam: U32, dups: List<&2, DB>, +ndup: U32, +dp: U32) -> PN & U32:
  match z:
    case True{}:
      (PN{lams, nlam, DB{loc, (ndup + 1 : U32), lab} <> dups, (ndup + 1 : U32), dp}, (ndup + 1 : U32))
    case False{}:
      (PN{lams, nlam, dups, ndup, dp}, f)

def st.dup.k(+f: U32, +loc: U32, +lab: U32, pn: PN) -> PN & U32:
  match pn:
    case PN{lams, +nlam, dups, ndup, dp}:
      st.dup.new(U32.is_eq(f, 0), f, loc, lab, lams, nlam, dups, ndup, dp)

def is.app(+hi: U32) -> Bool:
  U32.is_eq(W.tg(hi), 0) || U32.is_eq(W.tg(hi), 10)

def is.ctr(+hi: U32, +t: U32, +nam: U32) -> Bool:
  U32.is_eq(W.tg(hi), t) && U32.is_eq(W.ex(hi), nam)

def cell(h: Array<U32>, +lo: U32) -> Array<U32> & U32 & U32 & U32 & U32:
  W.rd2(h, lo, (lo + 1 : U32))

def is.con(+hi: U32) -> Bool:
  is.ctr(hi, 15, 3)

def is.nil(+hi: U32) -> Bool:
  is.ctr(hi, 13, 2)

def str.chr.ok(z: Bool, h: Array<U32>, +c: U32) -> Array<U32> & Maybe<&2, U32>:
  match z:
    case True{}:
      (h, Some{c})
    case False{}:
      (h, None{})

def str.chr.n(r: Array<U32> & U32 & U32) -> Array<U32> & Maybe<&2, U32>:
  (h, +a, b0) = r
  +b = {b0 : U32}
  str.chr.ok(U32.is_eq(W.tg(a), 30) && can.esc(b, 1), h, b)

def str.chr.k(z: Bool, h: Array<U32>, +hl: U32) -> Array<U32> & Maybe<&2, U32>:
  match z:
    case False{}:
      (h, None{})
    case True{}:
      str.chr.n(W.rd(h, hl))

# one list cell's head for the string test: its char, or none
def str.chr(h: Array<U32>, +hh: U32, +hl: U32) -> Array<U32> & Maybe<&2, U32>:
  str.chr.k(is.ctr(hh, 14, 4), h, hl)

# the list sugar's scan: (heap, string chars or none, elements, end word)
type LS is Data:
  LS{isstr: Bool, cs: List<&2, U32>, es: List<&2, Wd>, eh: U32, el: U32}

def str.out(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      str.out(t, rev.onto(esc(c, 1), acc))

# Steps
# =====

def em(w: PW(), +cs: List<&2, U32>) -> PW():
  (h, pn, pm, out, s) = w
  (h, pn, pm, rev.onto(cs, out), s)

def pe(s: String) -> PSel:
  PE{tx(s)}

def is.mat(+hi: U32) -> Bool:
  U32.is_eq(W.tg(hi), 12) || U32.is_eq(W.tg(hi), 31)

def mat.next.k(m: Bool, z: Bool, u: Bool, +hi: U32, +lo: U32, +d: U32) -> PSel:
  match m z u:
    case True{} _ _:
      PL{[PE{[59]}, PMat{hi, lo, d}]}
    case False{} True{} _:
      PL{[]}
    case False{} False{} True{}:
      PL{[PE{[59]}, PAt{lo, d}]}
    case False{} False{} False{}:
      PL{[PE{[59]}, PT{hi, lo, d}]}

# what follows a MAT/SWI link's value: the next link or the tail
def mat.next(+hi: U32, +lo: U32, +d: U32) -> PSel:
  mat.next.k(is.mat(hi), U32.is_eq(W.tg(hi), 30) && U32.is_eq(lo, 0), U32.is_eq(W.tg(hi), 32), hi, lo, d)

def sep.args.k(first: Bool, x: PSel, rest: List<&2, PSel>) -> List<&2, PSel>:
  match first:
    case True{}:
      x <> rest
    case False{}:
      PE{[44]} <> (x <> rest)

def sep.args(xs: List<&2, Wd>, +d: U32, first: Bool) -> List<&2, PSel>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Wd{+a, +b}, t}:
      sep.args.k(first, PT{a, b, d}, sep.args(t, d, False{}))

def ctr.default.k(+env: Env, +hi: U32, +d: U32, r: Array<U32> & List<&2, Wd>) -> Array<U32> & PSel:
  (h, ws) = r
  (h, PL{[PE{35 <> name.of(env, W.ex(hi))}, PE{[123]}, PArgs{ws, d, True{}}, PE{[125]}]})

def bj.lvl(z: Bool, +lvl: U32, +slen: U32, +d: U32) -> U32:
  match z:
    case True{}:
      u.pick(U32.is_gt((lvl - slen : U32), d), 0, (lvl - slen : U32))
    case False{}:
      0

def bj.upper(+nam: U32) -> List<&2, U32>:
  match nam:
    case 0:
      [95]
    case x:
      alpha(x, 65)

def bj.name.k(+t: U32, +nam: U32) -> List<&2, U32>:
  match t:
    case 42:
      alpha(nam, 97)
    case 43:
      List.append(&2, U32, bj.upper(nam), [8320])
    case x:
      List.append(&2, U32, bj.upper(nam), [8321])

# a BJV/BJ0/BJ1 in quoted mode: its ALO substitution, or its name
def bj.name(+t: U32, +lvl: U32, +slen: U32, +d: U32) -> List<&2, U32>:
  bj.name.k(t, bj.lvl(U32.is_gt(lvl, slen), lvl, slen, d))

def bj.dyn(+t: U32) -> U32:
  match t:
    case 42:
      1
    case 43:
      3
    case x:
      4

def bj.bound.k(z: Bool, +t: U32, +lab: U32, +bind: U32, +d: U32, +vh: U32, +vl: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      (h, PMode{0, 0, 0, W.sub.off(vh), vl, d})
    case False{}:
      (h, PMode{0, 0, 0, W.hd(bj.dyn(t), lab), bind, d})

def bj.bound(+t: U32, +lab: U32, +bind: U32, +d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +vh, vl0) = r
  +vl = {vl0 : U32}
  bj.bound.k(W.is.sub(vh), t, lab, bind, d, vh, vl, h)

def bj.found.k(z: Bool, +t: U32, +lab: U32, +lvl: U32, +slen: U32, +d: U32, +bind: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      (h, PE{bj.name(t, lvl, slen, d)})
    case False{}:
      bj.bound(t, lab, bind, d, W.rd(h, bind))

def bj.found(+t: U32, +lab: U32, +lvl: U32, +slen: U32, +d: U32, r: Array<U32> & U32) -> Array<U32> & PSel:
  (h, bind0) = r
  +bind = {bind0 : U32}
  bj.found.k(U32.is_zero(bind), t, lab, lvl, slen, d, bind, h)

def var.name(+t: U32, +loc: U32, +lab: U32) -> PSel:
  match t:
    case 1:
      PLam{loc}
    case x:
      PDupN{loc, lab}

def var.pick(z: Bool, +t: U32, +loc: U32, +lab: U32, +d: U32, +ch: U32, +cl: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      (h, PMode{0, 0, 0, W.sub.off(ch), cl, d})
    case False{}:
      (h, var.name(t, loc, lab))

def var.k(+t: U32, +loc: U32, +lab: U32, +d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +ch, cl0) = r
  +cl = {cl0 : U32}
  var.pick(U32.is_ne(loc, 0) && W.is.sub(ch), t, loc, lab, d, ch, cl, h)

def alo.k2(+ls: U32, +len: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +bh, bl0) = r
  +bl = {bl0 : U32}
  (h, PL{[PE{[64, 123]}, PMode{1, ls, len, bh, bl, 0}, PE{[125]}]})

def alo.k(+len: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +ls, tm0) = r
  +tm = {tm0 : U32}
  alo.k2(ls, len, W.rd(h, tm))

def uns.k3(+locf: U32, +locv: U32, +d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +bh, bl0) = r
  +bl = {bl0 : U32}
  (h, PL{[pe("! "), PLam{locf}, pe(" = λ "), PLam{locv}, pe(" ; "), PT{bh, bl, (d + 2 : U32)}]})

def uns.k2(+locf: U32, +d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, vh, locv0) = r
  +locv = {locv0 : U32}
  uns.k3(locf, locv, d, W.rd(h, locv))

def uns.k(+d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, fh, locf0) = r
  +locf = {locf0 : U32}
  uns.k2(locf, d, W.rd(h, locf))

def mat.n.k(+d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +nh, nl0) = r
  +nl = {nl0 : U32}
  (h, mat.next(nh, nl, d))

def fin.sep(+first: Bool) -> List<&2, U32>:
  match first:
    case True{}:
      [59]
    case False{}:
      []

def fin.v(+first: Bool, +nam: U32, +lab: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +vh, vl0) = r
  +vl = {vl0 : U32}
  (h, PL{[PE{fin.sep(first)}, PE{33 <> alpha(nam, 65)}, PE{38 <> pname(lab)}, PE{[61]}, PT{W.sub.off(vh), vl, 0}, PE{[59]}, PFin{False{}}]})

def fin.db(+first: Bool, r: Maybe<&2, DB>, h: Array<U32>) -> Array<U32> & PSel:
  match r:
    case None{}:
      (h, PL{[]})
    case Some{DB{+loc, +nam, +lab}}:
      fin.v(first, nam, lab, W.rd(h, loc))

def fin.k(+first: Bool, +dp: U32, ds: List<&2, DB>, +ndup: U32, h: Array<U32>) -> Array<U32> & PSel:
  fin.db(first, List.get(&2, DB, ds, U32.to_nat((ndup - 1 - dp : U32))), h)

def pn.dp.inc(pn: PN) -> PN:
  match pn:
    case PN{lams, nlam, dups, ndup, +dp}:
      PN{lams, nlam, dups, ndup, (dp + 1 : U32)}

def pn.dp(+pn: PN) -> U32:
  match pn:
    case PN{lams, nlam, dups, ndup, dp}:
      dp

def pn.ndup(+pn: PN) -> U32:
  match pn:
    case PN{lams, nlam, dups, ndup, dp}:
      ndup

def pn.dups(+pn: PN) -> List<&2, DB>:
  match pn:
    case PN{lams, nlam, dups, ndup, dp}:
      dups

def pm.quoted(+pm: PM) -> U32:
  match pm:
    case PM{qt, s, l}:
      qt

def fin.go.k(pn: PN, r: Array<U32> & PSel) -> Array<U32> & PN & PSel:
  (h, s) = r
  (h, pn, s)

# The printer
# ===========

def fin.go(z: Bool, +first: Bool, +pn: PN, h: Array<U32>) -> Array<U32> & PN & PSel:
  match z:
    case False{}:
      (h, pn, PL{[]})
    case True{}:
      fin.go.k(pn.dp.inc(pn), fin.k(first, pn.dp(pn), pn.dups(pn), pn.ndup(pn), h))

def lam.name(+qt: U32, +lo: U32, +d: U32) -> PSel:
  match qt:
    case 0:
      PLam{lo}
    case x:
      PE{alpha((d + 1 : U32), 97)}

def dup.steps(+qt: U32, +hi: U32, +lo: U32, +d: U32) -> PSel:
  match qt:
    case 0:
      PL{[PDupReg{lo, W.ex(hi)}, PAt{(lo + 1 : U32), d}]}
    case x:
      PL{[PE{33 <> alpha((d + 1 : U32), 65)}, PE{38 <> pname(W.ex(hi))}, PE{[61]}, PAt{lo, d}, PE{[59]}, PAt{(lo + 1 : U32), (d + 1 : U32)}]}

def print.k(w: PW()) -> Array<U32> & List<&2, U32>:
  (h, pn, pm, out, s) = w
  (h, out)
def nat.tail.k(z: Bool, +hi: U32, +lo: U32, +d: U32) -> PSel:
  match z:
    case True{}:
      PL{[]}
    case False{}:
      PL{[PE{[43]}, PT{hi, lo, d}]}

# the nat sugar's tail: nothing at #Zer, else +term
def nat.tail(+hi: U32, +lo: U32, +d: U32) -> PSel:
  nat.tail.k(U32.is_eq(W.tg(hi), 13) && U32.is_eq(W.ex(hi), 0), hi, lo, d)

def ctr.nat.k(+d: U32, r: Array<U32> & U32 & U32 & U32) -> Array<U32> & PSel:
  (h, +n, +th, tl0) = r
  +tl = {tl0 : U32}
  (h, PL{[PE{rev.onto(List.reverse(&2, U32, tx.num(n)), [110])}, nat.tail(th, tl, d)]})

def app.head.k(z: Bool, +hi: U32, +lo: U32, +d: U32) -> PSel:
  match z:
    case True{}:
      PL{[PE{[40]}, PT{hi, lo, d}, PE{[41]}]}
    case False{}:
      PT{hi, lo, d}

def app.head(+hi: U32, +lo: U32, +d: U32) -> PSel:
  app.head.k(U32.is_eq(W.tg(hi), 2), hi, lo, d)

def app.k(+d: U32, r: Array<U32> & U32 & U32 & List<&2, Wd>) -> Array<U32> & PSel:
  (h, +fh, +fl, args) = r
  (h, PL{[app.head(fh, fl, d), PE{[40]}, PArgs{args, d, True{}}, PE{[41]}]})

def alo.steps.k(+len: U32, +lo: U32, h: Array<U32>) -> Array<U32> & PSel:
  match len:
    case 0:
      alo.k2(0, 0, W.rd(h, lo))
    case n:
      alo.k(n, W.rd(h, lo))

def alo.steps(+hi: U32, +lo: U32, h: Array<U32>) -> Array<U32> & PSel:
  alo.steps.k(W.ex(hi), lo, h)

def mat.head.k(+t: U32, +env: Env, +hi: U32) -> List<&2, U32>:
  match t:
    case 31:
      tx.num(W.ex(hi))
    case x:
      mat.name(env, W.ex(hi))

def mat.head(+env: Env, +hi: U32) -> List<&2, U32>:
  mat.head.k(W.tg(hi), env, hi)

def ctr.or.none.k(z: Bool, +hi: U32, +lo: U32, +d: U32) -> PSel:
  match z:
    case True{}:
      PCtr{hi, lo, d}
    case False{}:
      PL{[]}

# print_term_ex / print_term_quoted_ex: the term, then its floating dups;
# answers the heap and the text, newest code point first
# answers the heap and the text
def ctr.or.none(+t: U32, +hi: U32, +lo: U32, +d: U32) -> PSel:
  ctr.or.none.k(U32.is_le(13, t) && U32.is_le(t, 29), hi, lo, d)
def subst.next(r: Array<U32> & U32 & U32) -> Array<U32> & Bool & U32:
  (h, nh, nl0) = r
  +nl = {nl0 : U32}
  (h, U32.is_zero(nl), nl)

# alo_subst_get: the idx-th bind node (0 = innermost)
def subst.get(k: Nat, r: Array<U32> & Bool & U32) -> Array<U32> & U32:
  match k:
    case 0n:
      (h, z, ls) = r
      (h, ls)
    case 1n+q:
      match r:
        case (h, True{}, ls):
          (h, 0)
        case (h, False{}, ls0):
          +ls = {ls0 : U32}
          subst.get(q, subst.next(W.rd(h, (ls + 1 : U32))))

def bj.steps.k(z: Bool, +t: U32, +lvl: U32, +lab: U32, +sub: U32, +slen: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      bj.found(t, lab, lvl, slen, d, subst.get(U32.to_nat((slen - lvl : U32)), (h, U32.is_zero(sub), sub)))
    case False{}:
      (h, PE{bj.name(t, lvl, slen, d)})

def bj.steps(+pm: PM, +t: U32, +lvl: U32, +lab: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  match pm:
    case PM{+qt, +sub, +slen}:
      bj.steps.k(U32.is_ne(qt, 0) && U32.is_gt(lvl, 0) && U32.is_le(lvl, slen), t, lvl, lab, sub, slen, d, h)

# alo_subst_get: the idx-th bind node (0 = innermost); r = (heap, ls is 0, ls)
def spine.next(acc: List<&2, Wd>, r: Array<U32> & U32 & U32 & U32 & U32) -> Array<U32> & Bool & U32 & U32 & List<&2, Wd>:
  (h, +ah, +al, +fh, fl0) = r
  +fl = {fl0 : U32}
  (h, is.app(fh), fh, fl, Wd{ah, al} <> acc)

# print_app's spine: (heap, head hi, head lo, args first to last)
def spine(k: Nat, r: Array<U32> & Bool & U32 & U32 & List<&2, Wd>) -> Array<U32> & U32 & U32 & List<&2, Wd>:
  match k:
    case 0n:
      (h, z, hi, lo, acc) = r
      (h, hi, lo, acc)
    case 1n+q:
      match r:
        case (h, False{}, hi, lo, acc):
          (h, hi, lo, acc)
        case (h, True{}, hi, lo0, acc):
          +lo = {lo0 : U32}
          spine(q, spine.next(acc, W.rd2(h, (lo + 1 : U32), lo)))

# print_app's spine: (heap, head hi, head lo, args first to last)
def words.next(+loc: U32, acc: List<&2, Wd>, r: Array<U32> & U32 & U32) -> Array<U32> & U32 & List<&2, Wd>:
  (h, +a, b0) = r
  +b = {b0 : U32}
  (h, (loc + 1 : U32), Wd{a, b} <> acc)

def words(k: Nat, r: Array<U32> & U32 & List<&2, Wd>) -> Array<U32> & List<&2, Wd>:
  match k:
    case 0n:
      (h, loc, acc) = r
      (h, List.reverse(&2, Wd, acc))
    case 1n+q:
      (h, +loc, acc) = r
      words(q, words.next(loc, acc, W.rd(h, loc)))

def ctr.default(+env: Env, +hi: U32, +lo: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  ctr.default.k(env, hi, d, words(U32.to_nat((W.tg(hi) - 13 : U32)), (h, lo, Nil{})))

def ctr.list.pick(s: Bool, l: Bool, c: Bool, +env: Env, +hi: U32, +lo: U32, +d: U32, cs: List<&2, U32>, es: List<&2, Wd>, h: Array<U32>) -> Array<U32> & PSel:
  match s l c:
    case True{} _ _:
      (h, PE{34 <> List.reverse(&2, U32, 34 <> str.out(cs, Nil{}))})
    case False{} True{} _:
      (h, PL{[PE{[91]}, PArgs{es, d, True{}}, PE{[93]}]})
    case False{} False{} True{}:
      (h, PL{[PAt{lo, d}, PE{[60, 62]}, PAt{(lo + 1 : U32), d}]})
    case False{} False{} False{}:
      ctr.default(env, hi, lo, d, h)

def ctr.list.k(+env: Env, +hi: U32, +lo: U32, +d: U32, r: Array<U32> & LS) -> Array<U32> & PSel:
  (h, ls) = r
  match ls:
    case LS{+isstr, cs, es, +eh, el}:
      ctr.list.pick(isstr && is.nil(eh), is.nil(eh), is.con(hi), env, hi, lo, d, cs, es, h)

def ctr.chr.ok(z: Bool, +env: Env, +hi: U32, +lo: U32, +d: U32, +c: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      (h, PE{39 <> rev.onto(List.reverse(&2, U32, esc(c, 0)), [39])})
    case False{}:
      ctr.default(env, hi, lo, d, h)

def ctr.chr.k(+env: Env, +hi: U32, +lo: U32, +d: U32, r: Array<U32> & U32 & U32) -> Array<U32> & PSel:
  (h, +a, b0) = r
  +b = {b0 : U32}
  ctr.chr.ok(U32.is_eq(W.tg(a), 30) && can.esc(b, 0), env, hi, lo, d, b, h)

def ctr.chr.go(z: Bool, +env: Env, +hi: U32, +lo: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  match z:
    case True{}:
      ctr.chr.k(env, hi, lo, d, W.rd(h, lo))
    case False{}:
      ctr.default(env, hi, lo, d, h)

# the words at loc .. loc + n - 1
def nat.next(+n: U32, r: Array<U32> & U32 & U32) -> Array<U32> & Bool & U32 & U32 & U32:
  (h, +a, b0) = r
  +b = {b0 : U32}
  (h, is.ctr(a, 14, 1), a, b, (n + 1 : U32))

# Nat sugar: the SUCs counted, and the word under them
def nat.count(k: Nat, r: Array<U32> & Bool & U32 & U32 & U32) -> Array<U32> & U32 & U32 & U32:
  match k:
    case 0n:
      (h, z, hi, lo, n) = r
      (h, n, hi, lo)
    case 1n+q:
      match r:
        case (h, False{}, hi, lo, n):
          (h, n, hi, lo)
        case (h, True{}, hi, lo0, n0):
          +lo = {lo0 : U32}
          +n = {n0 : U32}
          nat.count(q, nat.next(n, W.rd(h, lo)))

# Nat sugar: the SUCs counted, and the word under them
def LSt() -> Type:
  Array<U32> & Bool & U32 & U32 & Bool & List<&2, U32> & List<&2, Wd>

def lst.next2(+isstr: Bool, cs: List<&2, U32>, es: List<&2, Wd>, +ah: U32, +al: U32, +th: U32, +tl: U32, r: Array<U32> & Maybe<&2, U32>) -> LSt():
  (h, m) = r
  match m:
    case None{}:
      (h, is.con(th), th, tl, False{}, cs, Wd{ah, al} <> es)
    case Some{+c}:
      (h, is.con(th), th, tl, isstr, c <> cs, Wd{ah, al} <> es)

def lst.next(+isstr: Bool, cs: List<&2, U32>, es: List<&2, Wd>, r: Array<U32> & U32 & U32 & U32 & U32) -> LSt():
  (h, +ah, +al, +th, tl0) = r
  +tl = {tl0 : U32}
  lst.next2(isstr, cs, es, ah, al, th, tl, str.chr(h, ah, al))

def lst.scan(k: Nat, r: LSt()) -> Array<U32> & LS:
  match k:
    case 0n:
      (h, z, hi, lo, isstr, cs, es) = r
      (h, LS{isstr, List.reverse(&2, U32, cs), List.reverse(&2, Wd, es), hi, lo})
    case 1n+q:
      match r:
        case (h, False{}, hi, lo, isstr, cs, es):
          (h, LS{isstr, List.reverse(&2, U32, cs), List.reverse(&2, Wd, es), hi, lo})
        case (h, True{}, hi, lo0, isstr0, cs, es):
          +lo = {lo0 : U32}
          +isstr = {isstr0 : Bool}
          lst.scan(q, lst.next(isstr, cs, es, cell(h, lo)))

# the nat sugar's tail: nothing at #Zer, else +term
def ctr.steps.k(+nam: U32, +env: Env, +hi: U32, +lo: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  match nam:
    case 0:
      ctr.nat.k(d, nat.count(4294967295n, (h, is.ctr(hi, 14, 1), hi, lo, 0)))
    case 1:
      ctr.nat.k(d, nat.count(4294967295n, (h, is.ctr(hi, 14, 1), hi, lo, 0)))
    case 4:
      ctr.chr.go(U32.is_eq(W.tg(hi), 14), env, hi, lo, d, h)
    case 2:
      ctr.list.k(env, hi, lo, d, lst.scan(4294967295n, (h, is.con(hi), hi, lo, False{}, Nil{}, Nil{})))
    case 3:
      ctr.list.k(env, hi, lo, d, lst.scan(4294967295n, (h, is.con(hi), hi, lo, True{}, Nil{}, Nil{})))
    case x:
      ctr.default(env, hi, lo, d, h)

# print_ctr: the steps for a constructor
def ctr.steps(+env: Env, +hi: U32, +lo: U32, +d: U32, h: Array<U32>) -> Array<U32> & PSel:
  ctr.steps.k(W.ex(hi), env, hi, lo, d, h)

# the list sugar's scan: r = (heap, at a CON, word, string so far, chars, elements)
def w.at.k(pn: PN, pm: PM, out: List<&2, U32>, +d: U32, r: Array<U32> & U32 & U32) -> PW():
  (h, +hi, lo0) = r
  +lo = {lo0 : U32}
  (h, pn, pm, out, PT{hi, lo, d})

# the word at loc, into the register
def w.at(w: PW(), +loc: U32, +d: U32) -> PW():
  (h, pn, pm, out, s) = w
  w.at.k(pn, pm, out, d, W.rd(h, loc))

def w.hs(pn: PN, pm: PM, out: List<&2, U32>, r: Array<U32> & PSel) -> PW():
  (h, s) = r
  (h, pn, pm, out, s)

def w.lam.k(h: Array<U32>, pm: PM, out: List<&2, U32>, +base: U32, r: PN & U32) -> PW():
  (pn, nam0) = r
  +nam = {nam0 : U32}
  (h, pn, pm, rev.onto(alpha(nam, base), out), PL{[]})

def w.reg.k(h: Array<U32>, pm: PM, out: List<&2, U32>, r: PN & U32) -> PW():
  (pn, nam) = r
  (h, pn, pm, out, PL{[]})

def w.fin.k(pm: PM, out: List<&2, U32>, r: Array<U32> & PN & PSel) -> PW():
  (h, pn, s) = r
  (h, pn, pm, out, s)

def lam.find.k(z: Bool, +n: U32, +rest: U32) -> U32:
  match z:
    case True{}:
      n
    case False{}:
      rest
def lam.find(ls: List<&2, LB>, +loc: U32) -> U32:
  match ls:
    case Nil{}:
      0
    case Con{LB{+l, +n}, t}:
      lam.find.k(U32.is_eq(l, loc), n, lam.find(t, loc))

def dup.find(ds: List<&2, DB>, +loc: U32) -> U32:
  match ds:
    case Nil{}:
      0
    case Con{DB{+l, +n, b}, t}:
      lam.find.k(U32.is_eq(l, loc), n, dup.find(t, loc))

# print_state_lam: the lambda's name, new if unseen
def st.lam(+pn: PN, +loc: U32) -> PN & U32:
  match pn:
    case PN{+lams, nlam, dups, ndup, dp}:
      st.lam.k(lam.find(lams, loc), loc, pn)

# print_state_dup: the dup node's name, new if unseen
def st.dup(+pn: PN, +loc: U32, +lab: U32) -> PN & U32:
  match pn:
    case PN{lams, nlam, +dups, ndup, dp}:
      st.dup.k(dup.find(dups, loc), loc, lab, pn)

# Heap walks
# ==========

def pr(+k: Nat, +env: Env, +sel: PSel, w: PW()) -> PW():
  match k:
    case 0n:
      em(w, tx("<fuel>"))
    case 1n+q:
      match sel:
        case PT{+hi, +lo, +d}:
          pr(q, env, PTg{W.tg(hi), hi, lo, d}, w)
        case PAt{+loc, +d}:
          pr(q, env, PRun{}, w.at(w, loc, d))
        case PRun{}:
          (h, pn, pm, out, s0) = w
          +s = {s0 : PSel}
          pr(q, env, s, (h, pn, pm, out, PL{[]}))
        case PE{+cs}:
          em(w, cs)
        case PL{+xs}:
          match xs:
            case Nil{}:
              w
            case Con{+x, +t}:
              pr(q, env, PL{t}, pr(q, env, x, w))
        case PMode{+qt, +sub, +len, +hi, +lo, +d}:
          (h, pn, +pm, out, s) = w
          pr(q, env, PRest{pm}, pr(q, env, PT{hi, lo, d}, (h, pn, PM{qt, sub, u.pick(U32.is_ne(qt, 0), len, 0)}, out, s)))
        case PRest{+m}:
          (h, pn, pm, out, s) = w
          (h, pn, m, out, s)
        case PLam{+loc}:
          (h, pn, pm, out, s) = w
          w.lam.k(h, pm, out, 97, st.lam(pn, loc))
        case PDupN{+loc, +lab}:
          (h, pn, pm, out, s) = w
          w.lam.k(h, pm, out, 65, st.dup(pn, loc, lab))
        case PDupReg{+loc, +lab}:
          (h, pn, pm, out, s) = w
          w.reg.k(h, pm, out, st.dup(pn, loc, lab))
        case PVar{+loc, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, var.k(1, loc, 0, d, W.rd(h, loc))))
        case PDp{+t, +loc, +lab, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PE{u.pick(U32.is_eq(t, 3), 8320, 8321) <> Nil{}}, pr(q, env, PRun{}, w.hs(pn, pm, out, var.k(t, loc, lab, d, W.rd(h, loc)))))
        case PBj{+t, +lvl, +lab, +d}:
          (h, pn, +pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, bj.steps(pm, t, lvl, lab, d, h)))
        case PApp{+hi, +lo, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, app.k(d, spine(256n, (h, is.app(hi), hi, lo, Nil{})))))
        case PMat{+hi, +lo, +d}:
          pr(q, env, PL{[PE{mat.head(env, hi)}, PE{[58]}, PAt{lo, d}, PMatN{hi, lo, d}]}, w)
        case PMatN{+hi, +lo, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, mat.n.k(d, W.rd(h, (lo + 1 : U32)))))
        case PCtr{+hi, +lo, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, ctr.steps(env, hi, lo, d, h)))
        case PArgs{+xs, +d, +first}:
          pr(q, env, PL{sep.args(xs, d, first)}, w)
        case PAlo{+hi, +lo}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, alo.steps(hi, lo, h)))
        case PUns{+lo, +d}:
          (h, pn, pm, out, s) = w
          pr(q, env, PRun{}, w.hs(pn, pm, out, uns.k(d, W.rd(h, lo))))
        case PFin{+first}:
          (h, +pn, pm, out, s) = w
          pr(q, env, PRun{}, w.fin.k(pm, out, fin.go(U32.is_lt(pn.dp(pn), pn.ndup(pn)), first, pn, h)))
        # print_term_go, by tag
        case PTg{+t, +hi, +lo, +d}:
          match t:
            case 9:
              em(w, pname(W.ex(hi)))
            case 10:
              pr(q, env, PApp{hi, lo, d}, w)
            case 0:
              pr(q, env, PApp{hi, lo, d}, w)
            case 42:
              pr(q, env, PBj{42, lo, 0, d}, w)
            case 43:
              pr(q, env, PBj{43, lo, W.ex(hi), d}, w)
            case 44:
              pr(q, env, PBj{44, lo, W.ex(hi), d}, w)
            case 30:
              em(w, tx.num(lo))
            case 8:
              em(w, 64 <> name.of(env, W.ex(hi)))
            case 11:
              em(w, [38, 123, 125])
            case 40:
              em(w, [42])
            case 1:
              pr(q, env, PVar{lo, d}, w)
            case 3:
              pr(q, env, PDp{3, lo, W.ex(hi), d}, w)
            case 4:
              pr(q, env, PDp{4, lo, W.ex(hi), d}, w)
            case 2:
              (h, pn, +pm, out, s) = w
              pr(q, env, PL{[PE{[955]}, lam.name(pm.quoted(pm), lo, d), PE{[46]}, PAt{lo, (d + 1 : U32)}]}, (h, pn, pm, out, s))
            case 5:
              pr(q, env, PL{[PE{38 <> pname(W.ex(hi))}, PE{[123]}, PAt{lo, d}, PE{[44]}, PAt{(lo + 1 : U32), d}, PE{[125]}]}, w)
            case 6:
              (h, pn, +pm, out, s) = w
              pr(q, env, dup.steps(pm.quoted(pm), hi, lo, d), (h, pn, pm, out, s))
            case 12:
              pr(q, env, PL{[PE{[955, 123]}, PMat{hi, lo, d}, PE{[125]}]}, w)
            case 31:
              pr(q, env, PL{[PE{[955, 123]}, PMat{hi, lo, d}, PE{[125]}]}, w)
            case 32:
              pr(q, env, PL{[PE{[955, 123]}, PAt{lo, d}, PE{[125]}]}, w)
            case 33:
              pr(q, env, PL{[PE{[40]}, PAt{lo, d}, PE{32 <> List.append(&2, U32, op.sym(W.ex(hi)), [32])}, PAt{(lo + 1 : U32), d}, PE{[41]}]}, w)
            case 34:
              pr(q, env, PL{[PE{[38, 40]}, PAt{lo, d}, PE{[41, 123]}, PAt{(lo + 1 : U32), d}, PE{[44]}, PAt{(lo + 2 : U32), d}, PE{[125]}]}, w)
            case 35:
              pr(q, env, PL{[PE{[33, 40]}, PAt{lo, d}, PE{[41, 61]}, PAt{(lo + 1 : U32), d}, PE{[59]}, PAt{(lo + 2 : U32), d}]}, w)
            case 7:
              pr(q, env, PAlo{hi, lo}, w)
            case 36:
              pr(q, env, PL{[PE{[40]}, PAt{lo, d}, pe(" === "), PAt{(lo + 1 : U32), d}, PE{[41]}]}, w)
            case 37:
              pr(q, env, PL{[PE{[40]}, PAt{lo, d}, pe(" .&. "), PAt{(lo + 1 : U32), d}, PE{[41]}]}, w)
            case 38:
              pr(q, env, PL{[PE{[40]}, PAt{lo, d}, pe(" .|. "), PAt{(lo + 1 : U32), d}, PE{[41]}]}, w)
            case 39:
              pr(q, env, PUns{lo, d}, w)
            case 41:
              pr(q, env, PL{[PE{[8593]}, PAt{lo, d}]}, w)
            case x:
              pr(q, env, ctr.or.none(x, hi, lo, d), w)

# print_term_ex / print_term_quoted_ex: the term, then its floating dups;
# answers the heap and the text, newest code point first
# answers the heap and the text
def print(+env: Env, +qt: U32, h: Array<U32>, +hi: U32, +lo: U32) -> Array<U32> & List<&2, U32>:
  print.k(pr(4294967295n, env, PL{[PT{hi, lo, 0}, PFin{True{}}]}, (h, PN{Nil{}, 0, Nil{}, 0, 0}, PM{qt, 0, 0}, Nil{}, PL{[]})))

