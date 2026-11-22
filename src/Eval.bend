import Base
import ./Wnf.bend as W
import ./Print.bend as P

# hvm5bis: normalization and collapse, a port of the CNF and Eval
# sections of HVM4's src/hvm.c.
#
# Meaning.
# - snf (eval_normalize): reduce to WNF every heap location reachable
#   from the root, each once (a visited bitset), depth first, fields in
#   order; the root then reads as the normal form.
# - cnf (cnf_at): reduce to WNF, then lift the first SUP among the
#   fields to the top, cloning the other fields under its label; an ERA
#   anywhere erases the whole term; INC stays where it is. A lambda's
#   variable becomes the quoted BJV of its depth.
# - collapse (eval_collapse): a queue of branches ordered by key (SUP
#   depth, less INC credit), then by age. A branch whose cnf is a SUP
#   enqueues both sides one key deeper; an INC is unwrapped (key - 1,
#   credit + 1); an ERA is dropped; anything else is one output line.

# the machine outside WNF: (h, s, nx, it, fr, er, hl)
def M() -> Type:
  W.S()

def R() -> Type:
  W.S() & U32 & U32

# Heap access on the machine
# ==========================

def m.rd.k(s: Array<U32>, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, r: Array<U32> & U32 & U32) -> R():
  (h, hi, lo) = r
  ((h, s, nx, it, fr, er, hl), hi, lo)

def m.rd(m: M(), +loc: U32) -> R():
  (h, s, nx, it, fr, er, hl) = m
  m.rd.k(s, nx, it, fr, er, hl, W.rd(h, loc))

def m.wr(m: M(), +loc: U32, +hi: U32, +lo: U32) -> M():
  (h, s, nx, it, fr, er, hl) = m
  (W.wr(h, loc, hi, lo), s, nx, it, fr, er, hl)

# heap_alloc: the next n words (the location is the old nx)
def m.nx(+m: U32) -> U32:
  m

def m.alloc(m: M(), +n: U32) -> M() & U32:
  (h, s, nx0, it, fr, er, hl) = m
  +nx = {nx0 : U32}
  ((h, s, (nx + n : U32), it, fr, er, hl), nx)

# SNF
# ===

def bit.k(+loc: U32, r: Array<U32> & U32) -> Array<U32> & Bool:
  (a, w0) = r
  +w = {w0 : U32}
  +b = U32.shln(1, U32.to_nat(U32.and(loc, 31)))
  (Array.set(U32, a, U32.shrn(loc, 5n), U32.or(w, b)), U32.is_ne(U32.and(w, b), 0))

# uset_add: mark loc; answers whether it was marked before
def bit.add(a: Array<U32>, +loc: U32) -> Array<U32> & Bool:
  bit.k(loc, Array.get(U32, a, U32.shrn(loc, 5n)))

# (machine, seen, stack, loc, mode): mode 0 done, 1 go on
def NS() -> Type:
  M() & Array<U32> & List<&2, U32> & U32 & U32

def snf.push(k: Nat, +base: U32, +i: U32, st: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      st
    case 1n+q:
      snf.push(q, base, (i - 1 : U32), (base + i : U32) <> st)

def snf.after.a(+ari: U32, +tl: U32, m: M(), seen: Array<U32>, st: List<&2, U32>) -> NS():
  match ari:
    case 0:
      (m, seen, st, 0, 1)
    case n:
      (m, seen, snf.push(U32.to_nat((n - 1 : U32)), tl, (n - 1 : U32), st), tl, 1)

def snf.after.t(+t: U32, +ari: U32, +tl: U32, m: M(), seen: Array<U32>, st: List<&2, U32>) -> NS():
  match t:
    case 3:
      (m, seen, st, tl, 1)
    case 4:
      (m, seen, st, tl, 1)
    case x:
      snf.after.a(ari, tl, m, seen, st)

def snf.after.k(z: Bool, +t: U32, +tl: U32, m: M(), seen: Array<U32>, st: List<&2, U32>) -> NS():
  match z:
    case True{}:
      (m, seen, st, 0, 0)
    case False{}:
      snf.after.t(t, W.arity(t), tl, m, seen, st)

# after wnf_at: DP0/DP1 go to their dup expr, other nodes push fields
# 1.. (last first) and go to field 0
def snf.after(seen: Array<U32>, st: List<&2, U32>, r: R()) -> NS():
  ((h, s, nx, it, fr, +er, hl), +th, tl0) = r
  +tl = {tl0 : U32}
  snf.after.k(U32.is_ne(er, 0), W.tg(th), tl, (h, s, nx, it, fr, er, hl), seen, st)

def snf.visit(m: M(), st: List<&2, U32>, +loc: U32, r: Array<U32> & Bool) -> NS():
  (seen, b) = r
  match b:
    case True{}:
      (m, seen, st, 0, 1)
    case False{}:
      snf.after(seen, st, W.wnf.at(m, loc))

def snf.pop(m: M(), seen: Array<U32>, st: List<&2, U32>) -> NS():
  match st:
    case Nil{}:
      (m, seen, Nil{}, 0, 0)
    case Con{+x, t}:
      (m, seen, t, x, 1)

def snf.step(z: Bool, m: M(), seen: Array<U32>, st: List<&2, U32>, +loc: U32) -> NS():
  match z:
    case True{}:
      snf.pop(m, seen, st)
    case False{}:
      snf.visit(m, st, loc, bit.add(seen, loc))

def snf.go(k: Nat, n: NS()) -> NS():
  match k:
    case 0n:
      n
    case 1n+q:
      match n:
        case (m, seen, st, loc, 0):
          (m, seen, st, loc, 0)
        case (m, seen, st, loc0, md):
          +loc = {loc0 : U32}
          snf.go(q, snf.step(U32.is_zero(loc), m, seen, st, loc))

def snf.fin(n: NS()) -> M() & Array<U32>:
  (m, seen, st, loc, md) = n
  (m, seen)

# eval_normalize from the root location (seen: a cleared bitset)
def snf(m: M(), seen: Array<U32>, +root: U32) -> M() & Array<U32>:
  snf.fin(snf.go(Nat.mul(4294967295n, 65535n), (m, seen, [root], 0, 1)))

# CNF
# ===

type CS is Data:
  CAt{d: U32}
  CW{d: U32}
  CLamS{lo: U32, d: U32}
  CKids{nhi: U32, nlo: U32, ari: U32, i: U32, sidx: U32, d: U32}
  CKid{nhi: U32, nlo: U32, ari: U32, i: U32, sidx: U32, d: U32}
  CAfter{nhi: U32, nlo: U32, ari: U32, i: U32, sidx: U32, d: U32}
  CDone{nhi: U32, nlo: U32, ari: U32, sidx: U32}
  CRet{}

def cnf.sel(+er: U32, +d: U32) -> CS:
  match er:
    case 0:
      CW{d}
    case x:
      CRet{}

def cnf.wnf(+er: U32, m: M(), +hi: U32, +lo: U32) -> R():
  match er:
    case 0:
      W.wnf(m, hi, lo)
    case x:
      (m, hi, lo)

def cnf.lam.prep.k(+lo: U32, +lvl: U32, r: R()) -> R():
  (m, bh, bl) = r
  (m.wr(m, lo, W.sub.on(W.hd(42, 0)), lvl), bh, bl)

# the LAM case before its body: x ← BJV(level); answers the body
def cnf.lam.prep(m: M(), +lo: U32, +lvl: U32) -> R():
  cnf.lam.prep.k(lo, lvl, m.rd(m, lo))

def cnf.lam.inc.k(+lvl: U32, +bloc: U32, r: M() & U32) -> R():
  (m, il0) = r
  +il = {il0 : U32}
  (m.wr(m, il, W.hd(2, lvl), bloc), W.hd(41, 0), il)

def cnf.lam.inc(+lvl: U32, +bloc: U32, r: R()) -> R():
  (m, xh, xl) = r
  cnf.lam.inc.k(lvl, bloc, m.alloc(m.wr(m, bloc, xh, xl), 1))

def m.rd2.k(r: R(), s: W.S() & U32 & U32) -> M() & U32 & U32 & U32 & U32:
  (x, ah, al) = r
  ((h, ss, nx, it, fr, er, hl), bh, bl) = s
  ((h, ss, nx, it, fr, er, hl), ah, al, bh, bl)

def m.rd2.fin(+ah: U32, +al: U32, r: R()) -> M() & U32 & U32 & U32 & U32:
  (m, bh, bl) = r
  (m, ah, al, bh, bl)

def m.rd2.go(+loc: U32, r: R()) -> M() & U32 & U32 & U32 & U32:
  (m, ah, al) = r
  m.rd2.fin(ah, al, m.rd(m, (loc + 1 : U32)))

def m.rd2(m: M(), +loc: U32) -> M() & U32 & U32 & U32 & U32:
  m.rd2.go(loc, m.rd(m, loc))

def cnf.lam.sup.k(+lvl: U32, +lab: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32, r: M() & U32) -> R():
  (m, l00) = r
  +l0 = {l00 : U32}
  m = m.wr(m, l0, ah, al)
  m = m.wr(m, (l0 + 1 : U32), bh, bl)
  m = m.wr(m, (l0 + 2 : U32), W.hd(2, lvl), l0)
  m = m.wr(m, (l0 + 3 : U32), W.hd(2, lvl), (l0 + 1 : U32))
  (m, W.hd(5, lab), (l0 + 2 : U32))

def cnf.lam.sup(+lvl: U32, +lab: U32, r: M() & U32 & U32 & U32 & U32) -> R():
  (m, +ah, +al, +bh, bl00) = r
  +bl0 = {bl00 : U32}
  +bl = {bl0 : U32}
  cnf.lam.sup.k(lvl, lab, ah, al, bh, bl, m.alloc(m, 4))

def cnf.lam.fin.t(+t: U32, +lvl: U32, +bh: U32, +bl: U32, +bloc: U32, m: M()) -> R():
  match t:
    case 11:
      (m, W.hd(11, 0), 0)
    case 41:
      cnf.lam.inc(lvl, bloc, m.rd(m, bl))
    case 5:
      cnf.lam.sup(lvl, W.ex(bh), m.rd2(m, bl))
    case x:
      (m, W.hd(2, lvl), bloc)

def cnf.lam.fin.k(+lvl: U32, +bh: U32, +bl: U32, r: M() & U32) -> R():
  (m, bloc0) = r
  +bloc = {bloc0 : U32}
  cnf.lam.fin.t(W.tg(bh), lvl, bh, bl, bloc, m.wr(m, bloc, bh, bl))

# the LAM case after its body (r): the quoted lambda, or the ERA / INC /
# SUP it lifts
def cnf.lam.fin(+lvl: U32, r: R()) -> R():
  (m, +bh, bl0) = r
  +bl = {bl0 : U32}
  cnf.lam.fin.k(lvl, bh, bl, m.alloc(m, 1))

# is this tag one of cnf_at's nodes (fields walked, a SUP lifted)?
def cnf.node(+t: U32) -> Bool:
  match t:
    case 6:
      True{}
    case 0:
      True{}
    case 10:
      True{}
    case 12:
      True{}
    case 31:
      True{}
    case 32:
      True{}
    case 33:
      True{}
    case 34:
      True{}
    case 35:
      True{}
    case 36:
      True{}
    case 37:
      True{}
    case 38:
      True{}
    case 39:
      True{}
    case x:
      U32.is_le(14, x) && U32.is_le(x, 29)

def cnf.w.node(z: Bool, +t: U32, +hi: U32, +lo: U32, +d: U32) -> CS:
  match z:
    case True{}:
      CKids{hi, lo, W.arity(t), 0, 255, d}
    case False{}:
      CRet{}

# what cnf_at does with a WNF, by tag
def cnf.w.sel(+t: U32, +hi: U32, +lo: U32, +d: U32) -> CS:
  match t:
    case 2:
      CLamS{lo, d}
    case x:
      cnf.w.node(cnf.node(x), x, hi, lo, d)

def u.pick(b: Bool, +x: U32, +y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

# the next field, or the end of the fields
def cnf.kids.sel(z: Bool, +nhi: U32, +nlo: U32, +ari: U32, +i: U32, +sidx: U32, +d: U32) -> CS:
  match z:
    case True{}:
      CDone{nhi, nlo, ari, sidx}
    case False{}:
      CKid{nhi, nlo, ari, i, sidx, d}

# after field i: an ERA erases the node, else the next field
def cnf.after.sel(z: Bool, +t: U32, +nhi: U32, +nlo: U32, +ari: U32, +i: U32, +sidx: U32, +d: U32) -> CS:
  match z:
    case True{}:
      CRet{}
    case False{}:
      CKids{nhi, nlo, ari, (i + 1 : U32), u.pick(U32.is_eq(sidx, 255) && U32.is_eq(t, 5), i, sidx), d}

def cnf.after.arg(z: Bool, m: M(), +ch: U32, +cl: U32) -> R():
  match z:
    case True{}:
      (m, W.hd(11, 0), 0)
    case False{}:
      (m, ch, cl)
# cloning the non-SUP fields: (machine, i, fields of side 0, side 1), newest first
def CL() -> Type:
  M() & U32 & List<&2, P.Wd> & List<&2, P.Wd>

def cnf.cl.k2(+lab: U32, xs: List<&2, P.Wd>, ys: List<&2, P.Wd>, +i: U32, +ch: U32, +cl: U32, r: M() & U32) -> CL():
  (m, loc0) = r
  +loc = {loc0 : U32}
  (m.wr(m, loc, ch, cl), (i + 1 : U32), P.Wd{W.hd(3, lab), loc} <> xs, P.Wd{W.hd(4, lab), loc} <> ys)

def cnf.cl.k(+lab: U32, xs: List<&2, P.Wd>, ys: List<&2, P.Wd>, +i: U32, r: R()) -> CL():
  (m, ch, cl) = r
  cnf.cl.k2(lab, xs, ys, i, ch, cl, m.alloc(m, 1))

def cnf.cl.step(z: Bool, +nlo: U32, +lab: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32, st: CL()) -> CL():
  match z:
    case True{}:
      (m, +i0, xs, ys) = st
      +i = {i0 : U32}
      (m, (i + 1 : U32), P.Wd{ah, al} <> xs, P.Wd{bh, bl} <> ys)
    case False{}:
      (m, +i0, xs, ys) = st
      +i = {i0 : U32}
      cnf.cl.k(lab, xs, ys, i, m.rd(m, (nlo + i : U32)))
def cnf.cl(k: Nat, +nlo: U32, +sidx: U32, +lab: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32, st: CL()) -> CL():
  match k:
    case 0n:
      st
    case 1n+q:
      (m, +i, xs, ys) = st
      cnf.cl(q, nlo, sidx, lab, ah, al, bh, bl, cnf.cl.step(U32.is_eq(i, sidx), nlo, lab, ah, al, bh, bl, (m, i, xs, ys)))

def m.wrs(ws: List<&2, P.Wd>, m: M(), +loc: U32) -> M():
  match ws:
    case Nil{}:
      m
    case Con{P.Wd{+a, +b}, t}:
      m.wrs(t, m.wr(m, loc, a, b), (loc + 1 : U32))
def cnf.build.w3(+t: U32, +ext: U32, +nlo: U32, +n1: U32, +lab: U32, r: M() & U32) -> R():
  (m, sl0) = r
  +sl = {sl0 : U32}
  m = m.wr(m, sl, W.hd(t, ext), nlo)
  m = m.wr(m, (sl + 1 : U32), W.hd(t, ext), n1)
  (m, W.hd(5, lab), sl)

def cnf.build.w2(+t: U32, +ext: U32, +nlo: U32, +ari: U32, +lab: U32, ys: List<&2, P.Wd>, r: M() & U32) -> R():
  (m, n10) = r
  +n1 = {n10 : U32}
  cnf.build.w3(t, ext, nlo, n1, lab, m.alloc(m.wrs(ys, m, n1), 2))

def cnf.build.w(+t: U32, +ext: U32, +nlo: U32, +ari: U32, +lab: U32, st: CL()) -> R():
  (m, i, xs, ys) = st
  cnf.build.w2(t, ext, nlo, ari, lab, List.reverse(&2, P.Wd, ys), m.alloc(m.wrs(List.reverse(&2, P.Wd, xs), m, nlo), ari))

def cnf.build.s(+nhi: U32, +nlo: U32, +ari: U32, +sidx: U32, +lab: U32, r: M() & U32 & U32 & U32 & U32) -> R():
  (m, +ah, +al, +bh, bl00) = r
  +bl0 = {bl00 : U32}
  +bl = {bl0 : U32}
  cnf.build.w(W.tg(nhi), W.ex(nhi), nlo, ari, lab, cnf.cl(U32.to_nat(ari), nlo, sidx, lab, ah, al, bh, bl, (m, 0, Nil{}, Nil{})))

def cnf.build.k(+nhi: U32, +nlo: U32, +ari: U32, +sidx: U32, r: R()) -> R():
  (m, +sh, sl00) = r
  +sl0 = {sl00 : U32}
  +sl = {sl0 : U32}
  cnf.build.s(nhi, nlo, ari, sidx, W.ex(sh), m.rd2(m, sl))

# the node after its fields: itself, or the SUP lifted out of field sidx
def cnf.build(+nhi: U32, +nlo: U32, +ari: U32, +sidx: U32, m: M()) -> R():
  match sidx:
    case 255:
      (m, nhi, nlo)
    case x:
      cnf.build.k(nhi, nlo, ari, x, m.rd(m, (nlo + x : U32)))

# cnf_at: r is the term at depth d (CAt); the other selectors are the
# points inside cnf_at's loop over a node's fields
def cnf(+k: Nat, +sel: CS, r: R()) -> R():
  match k:
    case 0n:
      r
    case 1n+q:
      match sel:
        case CRet{}:
          r
        case CAt{+d}:
          ((h, s, nx, it, fr, +er, hl), +hi, lo0) = r
          +lo = {lo0 : U32}
          cnf(q, cnf.sel(er, d), cnf.wnf(er, (h, s, nx, it, fr, er, hl), hi, lo))
        case CW{+d}:
          (m, +hi, lo0) = r
          +lo = {lo0 : U32}
          cnf(q, cnf.w.sel(W.tg(hi), hi, lo, d), (m, hi, lo))
        case CLamS{+lo, +d}:
          (m, a, b) = r
          cnf.lam.fin((d + 1 : U32), cnf(q, CAt{(d + 1 : U32)}, cnf.lam.prep(m, lo, (d + 1 : U32))))
        case CKids{+nhi, +nlo, +ari, +i, +sidx, +d}:
          cnf(q, cnf.kids.sel(U32.is_eq(i, ari), nhi, nlo, ari, i, sidx, d), r)
        case CDone{+nhi, +nlo, +ari, +sidx}:
          (m, a, b) = r
          cnf.build(nhi, nlo, ari, sidx, m)
        case CKid{+nhi, +nlo, +ari, +i, +sidx, +d}:
          (m, a, b) = r
          cnf(q, CAfter{nhi, nlo, ari, i, sidx, d}, cnf(q, CAt{d}, m.rd(m, (nlo + i : U32))))
        case CAfter{+nhi, +nlo, +ari, +i, +sidx, +d}:
          (m, +ch, cl0) = r
          +cl = {cl0 : U32}
          cnf(q, cnf.after.sel(U32.is_eq(W.tg(ch), 11), W.tg(ch), nhi, nlo, ari, i, sidx, d), cnf.after.arg(U32.is_eq(W.tg(ch), 11), m.wr(m, (nlo + i : U32), ch, cl), ch, cl))

# Collapse
# ========

# a branch: its order key, age, key (SUP depth), INC credit, location
type Tk is Data:
  Tk{ok: U32, seq: U32, key: U32, cr: U32, loc: U32}

# the queue: a leftist heap on (order key, age)
type Q is Data:
  QE{}
  QN{rank: U32, t: Tk, l: Q, r: Q}

def tk.lt(+a: Tk, +b: Tk) -> Bool:
  match a b:
    case Tk{+ao, +as, ak, ac, al} Tk{+bo, +bs, bk, bc, bl}:
      U32.is_lt(ao, bo) || (U32.is_eq(ao, bo) && U32.is_lt(as, bs))

# is a's top before b's (an empty queue is last)?
def q.lt(+a: Q, +b: Q) -> Bool:
  match a b:
    case QE{} _:
      False{}
    case QN{ra, ta, la, rra} QE{}:
      True{}
    case QN{ra, +ta, la, rra} QN{rb, +tb, lb, rrb}:
      tk.lt(ta, tb)

def q.rank(+a: Q) -> U32:
  match a:
    case QE{}:
      0
    case QN{+r, t, l, rr}:
      r

def ord.key(+key: U32, +cr: U32) -> U32:
  u.pick(U32.is_gt(key, U32.div(cr, 16)), (key - U32.div(cr, 16) : U32), 0)
def tk.new(+key: U32, +cr: U32, +seq: U32, +loc: U32) -> Tk:
  Tk{ord.key(key, cr), seq, key, cr, loc}

# one branch: cnf until it is not an INC; (machine, word, key, credit, mode)
# mode 0: cnf the word next; 1 a SUP; 2 an ERA; 3 a line to print
def PB() -> Type:
  M() & U32 & U32 & U32 & U32 & U32

def proc.inc(+key: U32, +cr: U32, r: R()) -> PB():
  (m, bh, bl) = r
  (m, bh, bl, u.pick(U32.is_gt(key, 0), (key - 1 : U32), 0), u.pick(U32.is_lt(cr, 128), (cr + 1 : U32), cr), 0)

def proc.t(+t: U32, m: M(), +th: U32, +tl: U32, +key: U32, +cr: U32) -> PB():
  match t:
    case 41:
      proc.inc(key, cr, m.rd(m, tl))
    case 5:
      (m, th, tl, key, cr, 1)
    case 11:
      (m, th, tl, key, cr, 2)
    case x:
      (m, th, tl, key, cr, 3)

def proc.er(z: Bool, m: M(), +th: U32, +tl: U32, +key: U32, +cr: U32) -> PB():
  match z:
    case True{}:
      (m, th, tl, key, cr, 2)
    case False{}:
      proc.t(W.tg(th), m, th, tl, key, cr)

def proc.step(+key: U32, +cr: U32, r: R()) -> PB():
  ((h, s, nx, it, fr, +er, hl), +th, tl0) = r
  +tl = {tl0 : U32}
  proc.er(U32.is_ne(er, 0), (h, s, nx, it, fr, er, hl), th, tl, key, cr)

def proc(k: Nat, st: PB()) -> PB():
  match k:
    case 0n:
      st
    case 1n+q:
      match st:
        case (m, hi0, lo0, key0, cr0, 0):
          +hi = {hi0 : U32}
          +lo = {lo0 : U32}
          +key = {key0 : U32}
          +cr = {cr0 : U32}
          proc(q, proc.step(key, cr, cnf(4294967295n, CAt{0}, (m, hi, lo))))
        case x:
          x

# the collapse's configuration: line limit (4294967295: none), show the
# interaction count after each line, print nothing
type Cfg is Data:
  Cfg{limit: U32, stats: Bool, silent: Bool}

def cfg.limit(+c: Cfg) -> U32:
  match c:
    case Cfg{l, s, q}:
      l

# (machine, queue, printed, next age, output newest first, mode 0 done 1 go)
def CO() -> Type:
  M() & Q & U32 & U32 & List<&2, U32> & U32

def it.of(m: M()) -> M() & Nat:
  (h, s, nx, +it, fr, er, hl) = m
  ((h, s, nx, it, fr, er, hl), it)

def col.itrs(z: Bool, +it: Nat) -> List<&2, U32>:
  match z:
    case True{}:
      List.append(&2, U32, [32, 27, 91, 50, 109, 35], List.append(&2, U32, P.tx(Nat.show(it)), [27, 91, 48, 109, 10]))
    case False{}:
      [10]

def col.line.k(+env: P.Env, +stats: Bool, +it: Nat, s: Array<U32>, +nx: U32, +fr: U32, +er: U32, +hl: U32, r: Array<U32> & List<&2, U32>) -> M() & List<&2, U32>:
  (h, txt) = r
  ((h, s, nx, it, fr, er, hl), List.append(&2, U32, List.reverse(&2, U32, col.itrs(stats, it)), txt))

def col.line(+env: P.Env, +stats: Bool, m: M(), +hi: U32, +lo: U32) -> M() & List<&2, U32>:
  (h, s, nx, +it, fr, er, hl) = m
  col.line.k(env, stats, it, s, nx, fr, er, hl, P.print(env, 1, h, hi, lo))

def col.out.k(q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, r: M() & List<&2, U32>) -> CO():
  (m, txt) = r
  (m, q, pr, seq, List.append(&2, U32, txt, out), 1)

# the machine and the text, newest code point first
def col.out(z: Bool, +env: P.Env, +cfg: Cfg, m: M(), q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, +hi: U32, +lo: U32) -> CO():
  match z:
    case True{}:
      match cfg:
        case Cfg{l, +st, si}:
          col.out.k(q, pr, seq, out, col.line(env, st, m, hi, lo))
    case False{}:
      (m, q, pr, seq, out, 1)

def cfg.silent(+c: Cfg) -> Bool:
  match c:
    case Cfg{l, s, si}:
      si

def col.er(m: M()) -> M() & U32:
  (h, s, nx, it, fr, +er, hl) = m
  ((h, s, nx, it, fr, er, hl), er)

def col.fin(st: CO()) -> M() & List<&2, U32>:
  (m, qu, pr, seq, out, md) = st
  (m, out)
def q.pick(z: Bool, +a: Q, +b: Q) -> Q:
  match z:
    case True{}:
      a
    case False{}:
      b

def q.min(+a: Q, +b: Q) -> Q:
  q.pick(q.lt(b, a), b, a)

def q.max(+a: Q, +b: Q) -> Q:
  q.pick(q.lt(b, a), a, b)

def q.mk.k(z: Bool, +t: Tk, +a: Q, +b: Q) -> Q:
  match z:
    case True{}:
      QN{(q.rank(b) + 1 : U32), t, a, b}
    case False{}:
      QN{(q.rank(a) + 1 : U32), t, b, a}

def q.mk(+t: Tk, +a: Q, +b: Q) -> Q:
  q.mk.k(U32.is_ge(q.rank(a), q.rank(b)), t, a, b)

def q.merge(k: Nat, +a: Q, +b: Q) -> Q:
  match k:
    case 0n:
      a
    case 1n+p:
      match a b:
        case QE{} x:
          x
        case x QE{}:
          x
        case QN{r, +t, +l, +rr} y:
          q.mk(t, l, q.merge(p, q.min(rr, y), q.max(rr, y)))

def q.ins(+t: Tk, +a: Q) -> Q:
  q.merge(256n, q.min(QN{1, t, QE{}, QE{}}, a), q.max(QN{1, t, QE{}, QE{}}, a))

def col.done.k(+md: U32, +env: P.Env, +cfg: Cfg, m: M(), q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, +hi: U32, +lo: U32, +key: U32, +cr: U32) -> CO():
  match md:
    case 1:
      (m, q.ins(tk.new((key + 1 : U32), cr, (seq + 1 : U32), (lo + 1 : U32)), q.ins(tk.new((key + 1 : U32), cr, seq, lo), q)), pr, (seq + 2 : U32), out, 1)
    case 2:
      (m, q, pr, seq, out, 1)
    case x:
      col.out(U32.is_le((pr + 1 : U32), cfg.limit(cfg)) && Bool.not(cfg.silent(cfg)), env, cfg, m, q, (pr + 1 : U32), seq, out, hi, lo)

def col.done(+env: P.Env, +cfg: Cfg, q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, st: PB()) -> CO():
  (m, +hi, +lo, +key, +cr, md0) = st
  +md = {md0 : U32}
  col.done.k(md, env, cfg, m, q, pr, seq, out, hi, lo, key, cr)

def col.task.k(+env: P.Env, +cfg: Cfg, q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, +key: U32, +cr: U32, r: R()) -> CO():
  (m, bh, bl) = r
  col.done(env, cfg, q, pr, seq, out, proc(4294967295n, (m, bh, bl, key, cr, 0)))

def col.task(+env: P.Env, +cfg: Cfg, m: M(), q: Q, +pr: U32, +seq: U32, out: List<&2, U32>, +t: Tk) -> CO():
  match t:
    case Tk{o, s, +key, +cr, +loc}:
      col.task.k(env, cfg, q, pr, seq, out, key, cr, m.rd(m, loc))

def col.pop(+env: P.Env, +cfg: Cfg, m: M(), q: Q, +pr: U32, +seq: U32, out: List<&2, U32>) -> CO():
  match q:
    case QE{}:
      (m, QE{}, pr, seq, out, 0)
    case QN{r, +t, +l, +rr}:
      col.task(env, cfg, m, q.merge(256n, q.min(l, rr), q.max(l, rr)), pr, seq, out, t)

def col.step(z: Bool, +env: P.Env, +cfg: Cfg, m: M(), q: Q, +pr: U32, +seq: U32, out: List<&2, U32>) -> CO():
  match z:
    case True{}:
      (m, q, pr, seq, out, 0)
    case False{}:
      col.pop(env, cfg, m, q, pr, seq, out)

def col.go.er(+env: P.Env, +cfg: Cfg, r: M() & U32, qu: Q, +pr: U32, +seq: U32, out: List<&2, U32>) -> CO():
  (m, er0) = r
  +er = {er0 : U32}
  col.step(U32.is_ne(er, 0) || U32.is_ge(pr, cfg.limit(cfg)), env, cfg, m, qu, pr, seq, out)

def col.go(k: Nat, +env: P.Env, +cfg: Cfg, st: CO()) -> CO():
  match k:
    case 0n:
      st
    case 1n+q:
      match st:
        case (m, qu, pr0, seq0, out, 1):
          +pr = {pr0 : U32}
          +seq = {seq0 : U32}
          col.go(q, env, cfg, col.go.er(env, cfg, col.er(m), qu, pr, seq, out))
        case x:
          x

# eval_collapse from the root location: the machine and the text
def collapse(+env: P.Env, +cfg: Cfg, m: M(), +root: U32) -> M() & List<&2, U32>:
  col.fin(col.go(Nat.mul(4294967295n, 65535n), env, cfg, (m, QN{1, tk.new(0, 0, 0, root), QE{}, QE{}}, 0, 1, Nil{}, 1)))
