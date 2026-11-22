import Base

# hvm5bis: a port of HVM4 (HigherOrderCO) to Bend; see NOTICE and
# README.md (HVM4 has no license file: no license is claimed here).
#
# Wnf: terms, the heap and the weak-normal-form evaluator, after the
# Term, Heap and WNF sections of HVM4's src/hvm.c (rev 6defdfc7).
#
# A term is HVM4's 64-bit word split in two U32 halves:
#   hi = sub << 31 | tag << 24 | ext      (sub: the substitution bit)
#   lo = val
# The heap is one Array<U32>; word `loc` lives at slots 2*loc (hi) and
# 2*loc + 1 (lo). Word 0 is never allocated, as in HVM4.
#
# Tags (as in hvm.c):
#   APP 0  VAR 1  LAM 2  DP0 3  DP1 4  SUP 5  DUP 6  ALO 7  REF 8
#   NAM 9  DRY 10 ERA 11 MAT 12 C00..C16 13..29  NUM 30  SWI 31
#   USE 32 OP2 33 DSU 34 DDU 35 EQL 36 AND 37 OR 38 UNS 39 ANY 40
#   INC 41 BJV 42 BJ0 43 BJ1 44; frames F_OP2_NUM 67, F_EQL_R 69.
#
# Every state is threaded linearly through tuples, which Bend keeps in
# registers. The WNF machine W is
#   (h, s, sp, nx, it, fr, er, md, th, tl, hl)
# h the heap, s the stack (two slots a frame), sp its frames, nx the
# next free word, it the interaction count, fr the fresh-name counter,
# er an error code (0 none), md the mode (0 enter, 1 apply, 2 done),
# (th, tl) the term in hand and hl the heap's last usable word.
# A rule returns R = (h, nx, it, th, tl); k.ent / k.app put it back.

# Errors (er): 1 cannot apply a number, 2 cannot apply a constructor,
# 3 out of heap memory, 4 WNF stack overflow, 5 out of fuel.

def W() -> Type:
  Array<U32> & Array<U32> & U32 & U32 & Nat & U32 & U32 & U32 & U32 & U32 & U32

def R() -> Type:
  Array<U32> & U32 & Nat & U32 & U32

# S: the machine outside WNF: (h, s, nx, it, fr, er, hl)
def S() -> Type:
  Array<U32> & Array<U32> & U32 & Nat & U32 & U32 & U32

# Term words
# ==========

def tg(+hi: U32) -> U32:
  U32.and(U32.shrn(hi, 24n), 127)

def ex(+hi: U32) -> U32:
  U32.and(hi, 16777215)

def hd(+tag: U32, +ext: U32) -> U32:
  U32.or(U32.shln(tag, 24n), U32.and(ext, 16777215))

def sub.on(+hi: U32) -> U32:
  U32.or(hi, 2147483648)

def sub.off(+hi: U32) -> U32:
  U32.and(hi, 2147483647)

def is.sub(+hi: U32) -> Bool:
  U32.is_ne(U32.and(hi, 2147483648), 0)

# LAM_ERA_MASK: the binder is unused
def is.era(+hi: U32) -> Bool:
  U32.is_ne(U32.and(hi, 8388608), 0)

def is.ctr(+t: U32) -> Bool:
  U32.is_le(13, t) && U32.is_le(t, 29)

def arity.ctr(z: Bool, +t: U32) -> U32:
  match z:
    case True{}:
      (t - 13 : U32)
    case False{}:
      0

# Heap
# ====

# TERM_ARITY
def arity(+t: U32) -> U32:
  match t:
    case 0:
      2
    case 2:
      1
    case 5:
      2
    case 6:
      2
    case 10:
      2
    case 12:
      2
    case 31:
      2
    case 32:
      1
    case 33:
      2
    case 34:
      3
    case 35:
      3
    case 36:
      2
    case 37:
      2
    case 38:
      2
    case 39:
      1
    case 41:
      1
    case x:
      arity.ctr(is.ctr(x), x)

def wr(h: Array<U32>, +loc: U32, +hi: U32, +lo: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, h, U32.shl(loc), hi), U32.or(U32.shl(loc), 1), lo)

def rd.lo(+hi: U32, r: Array<U32> & U32) -> Array<U32> & U32 & U32:
  (h, lo) = r
  (h, hi, lo)

def rd.hi(+loc: U32, r: Array<U32> & U32) -> Array<U32> & U32 & U32:
  (h, +hi) = r
  rd.lo(hi, Array.get(U32, h, U32.or(U32.shl(loc), 1)))

# heap_read: the word at loc
def rd(h: Array<U32>, +loc: U32) -> Array<U32> & U32 & U32:
  rd.hi(loc, Array.get(U32, h, U32.shl(loc)))

def rd2.k(+ah: U32, +al: U32, r: Array<U32> & U32 & U32) -> Array<U32> & U32 & U32 & U32 & U32:
  (h, bh, bl) = r
  (h, ah, al, bh, bl)

def rd2.go(+lb: U32, r: Array<U32> & U32 & U32) -> Array<U32> & U32 & U32 & U32 & U32:
  (h, ah, al) = r
  rd2.k(ah, al, rd(h, lb))

# two words, at la and lb
def rd2(h: Array<U32>, +la: U32, +lb: U32) -> Array<U32> & U32 & U32 & U32 & U32:
  rd2.go(lb, rd(h, la))

def op2.mod(z: Bool, +a: U32, +b: U32) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      U32.mod(a, b)

def b2u(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

# Machine plumbing
# ================

# OP2 on two U32s (term_op2_u32); shifts mask their count as x86 does
def op2(+o: U32, +a: U32, +b: U32) -> U32:
  match o:
    case 0:
      (a + b : U32)
    case 1:
      (a - b : U32)
    case 2:
      (a * b : U32)
    case 3:
      U32.div(a, b)
    case 4:
      op2.mod(U32.is_zero(b), a, b)
    case 5:
      U32.and(a, b)
    case 6:
      U32.or(a, b)
    case 7:
      U32.xor(a, b)
    case 8:
      U32.shln(a, U32.to_nat(U32.and(b, 31)))
    case 9:
      U32.shrn(a, U32.to_nat(U32.and(b, 31)))
    case 10:
      U32.not(b)
    case 11:
      b2u(U32.is_eq(a, b))
    case 12:
      b2u(U32.is_ne(a, b))
    case 13:
      b2u(U32.is_lt(a, b))
    case 14:
      b2u(U32.is_le(a, b))
    case 15:
      b2u(U32.is_gt(a, b))
    case 16:
      b2u(U32.is_ge(a, b))
    case x:
      0

def k.ent(s: Array<U32>, +sp: U32, +fr: U32, +er: U32, +hl: U32, r: R()) -> W():
  (h, nx, it, th, tl) = r
  (h, s, sp, nx, it, fr, er, 0, th, tl, hl)

def k.app(s: Array<U32>, +sp: U32, +fr: U32, +er: U32, +hl: U32, r: R()) -> W():
  (h, nx, it, th, tl) = r
  (h, s, sp, nx, it, fr, er, 1, th, tl, hl)

# heap_subst_cop: X[side] is returned, the other side is left in loc
def cop(+side: U32, h: Array<U32>, +loc: U32, +r0h: U32, +r0l: U32, +r1h: U32, +r1l: U32, +nx: U32, it: Nat) -> R():
  match side:
    case 0:
      (wr(h, loc, sub.on(r1h), r1l), nx, it, r0h, r0l)
    case x:
      (wr(h, loc, sub.on(r0h), r0l), nx, it, r1h, r1l)

def era(h: Array<U32>, +nx: U32, it: Nat) -> R():
  (h, nx, 1n+it, hd(11, 0), 0)

def num(h: Array<U32>, +nx: U32, it: Nat, +n: U32) -> R():
  (h, nx, 1n+it, hd(30, 0), n)

# Interactions: APP
# =================

# (λx.f a) -> x ← a; f
def app.lam.k(z: Bool, +loc: U32, +ah: U32, +al: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  match z:
    case True{}:
      (h, bh, bl) = r
      (h, nx, it, bh, bl)
    case False{}:
      (h, bh, bl) = r
      (wr(h, loc, sub.on(ah), al), nx, it, bh, bl)

def app.lam(h: Array<U32>, +nx: U32, it: Nat, +th: U32, +tl: U32, +ah: U32, +al: U32) -> R():
  app.lam.k(is.era(th), tl, ah, al, nx, 1n+it, rd(h, tl))

# (&L{f,g} a) -> ! A &L = a; &L{(f A₀),(g A₁)}
def app.sup.k(+app: U32, +lab: U32, +sl: U32, +ah: U32, +al: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, t1h, t1l) = r
  +a1 = (nx + 1 : U32)
  h = wr(h, nx, ah, al)
  h = wr(h, (sl + 1 : U32), hd(3, lab), nx)
  h = wr(h, a1, t1h, t1l)
  h = wr(h, (nx + 2 : U32), hd(4, lab), nx)
  h = wr(h, app, hd(0, 0), sl)
  h = wr(h, (app + 1 : U32), hd(0, 0), a1)
  (h, (nx + 3 : U32), it, hd(5, lab), app)

def app.sup(h: Array<U32>, +nx: U32, it: Nat, +app: U32, +th: U32, +tl: U32, +ah: U32, +al: U32) -> R():
  app.sup.k(app, ex(th), tl, ah, al, nx, 1n+it, rd(h, (tl + 1 : U32)))

# (↑f x) -> ↑(f x)
def app.inc.k(+app: U32, +il: U32, +ih: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, fh, fl) = r
  h = wr(h, app, fh, fl)
  h = wr(h, il, hd(0, 0), app)
  (h, nx, it, ih, il)

def app.inc(h: Array<U32>, +nx: U32, it: Nat, +app: U32, +th: U32, +tl: U32) -> R():
  app.inc.k(app, tl, th, nx, 1n+it, rd(h, tl))

# Interactions: MAT / SWI
# =======================

# (λ{#K:h; m} &L{a,b}) -> ! H &L = h; ! M &L = m; &L{(λ{..}₀ a),(λ{..}₁ b)}
def mat.sup.k2(+fh: U32, +fl: U32, +lab: U32, +sl: U32, +nx: U32, it: Nat, +ah: U32, +al: U32, r: Array<U32> & U32 & U32) -> R():
  (h, bh, bl) = r
  h = wr(h, nx, fh, fl)
  h = wr(h, (nx + 1 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 2 : U32), ah, al)
  h = wr(h, (nx + 3 : U32), hd(4, lab), nx)
  h = wr(h, (nx + 4 : U32), bh, bl)
  h = wr(h, sl, hd(0, 0), (nx + 1 : U32))
  h = wr(h, (sl + 1 : U32), hd(0, 0), (nx + 3 : U32))
  (h, (nx + 5 : U32), it, hd(5, lab), sl)

def mat.sup.k1(+fh: U32, +fl: U32, +lab: U32, +sl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, ah, al) = r
  mat.sup.k2(fh, fl, lab, sl, nx, it, ah, al, rd(h, (sl + 1 : U32)))

def mat.sup(h: Array<U32>, +nx: U32, it: Nat, +fh: U32, +fl: U32, +th: U32, +tl: U32) -> R():
  mat.sup.k1(fh, fl, ex(th), tl, nx, 1n+it, rd(h, tl))

# (λ{...} ↑x) -> ↑(λ{...} x)
def mat.inc.k(+fh: U32, +fl: U32, +il: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, xh, xl) = r
  h = wr(h, nx, fh, fl)
  h = wr(h, (nx + 1 : U32), xh, xl)
  h = wr(h, il, hd(0, 0), nx)
  (h, (nx + 2 : U32), it, hd(41, 0), il)

def mat.inc(h: Array<U32>, +nx: U32, it: Nat, +fh: U32, +fl: U32, +tl: U32) -> R():
  mat.inc.k(fh, fl, tl, nx, 1n+it, rd(h, tl))

# (λ{#K:h; m} #L{..}) -> (m #L{..})  (MIS; also NUM-MIS)
def mat.mis.k(+ml: U32, +th: U32, +tl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, gh, gl) = r
  h = wr(h, ml, gh, gl)
  h = wr(h, (ml + 1 : U32), th, tl)
  (h, nx, it, hd(0, 0), ml)

def ret(+nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, xh, xl) = r
  (h, nx, it, xh, xl)

# the arguments past the second: each a fresh APP over the last
def mat.ctr.go(k: Nat, +cl: U32, +i: U32, +at: U32, +rh: U32, +rl: U32, r: Array<U32> & U32 & U32) -> Array<U32> & U32 & U32:
  match k:
    case 0n:
      (h, xh, xl) = r
      (h, rh, rl)
    case 1n+p:
      (h, xh, xl) = r
      h = wr(h, at, rh, rl)
      h = wr(h, (at + 1 : U32), xh, xl)
      mat.ctr.go(p, cl, (i + 1 : U32), (at + 2 : U32), hd(0, 0), at, rd(h, (cl + i + 1 : U32)))

def mat.ctr.fin(+nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, rh, rl) = r
  (h, nx, it, rh, rl)

def mat.ctr.h3(+ari: U32, +cl: U32, +nx: U32, it: Nat, h: Array<U32>) -> R():
  match ari:
    case 2:
      (h, nx, it, hd(0, 0), cl)
    case n:
      +k = (n - 2 : U32)
      mat.ctr.fin((nx + k + k : U32), it, mat.ctr.go(U32.to_nat(k), cl, 2, nx, hd(0, 0), cl, rd(h, (cl + 2 : U32))))

def mat.ctr.h2(+ari: U32, +cl: U32, +nx: U32, it: Nat, +ml: U32, r: Array<U32> & U32 & U32) -> R():
  match ari:
    case 1:
      (h, a1h, a1l) = r
      (h, nx, it, hd(0, 0), ml)
    case n:
      (h, a1h, a1l) = r
      h = wr(h, cl, hd(0, 0), ml)
      h = wr(h, (cl + 1 : U32), a1h, a1l)
      mat.ctr.h3(n, cl, nx, it, h)

def mat.ctr.h1(+ari: U32, +ml: U32, +cl: U32, +nx: U32, it: Nat, +rh: U32, +rl: U32, r: Array<U32> & U32 & U32) -> R():
  (h, a0h, a0l) = r
  h = wr(h, ml, rh, rl)
  h = wr(h, (ml + 1 : U32), a0h, a0l)
  mat.ctr.h2(ari, cl, nx, it, ml, rd(h, (cl + 1 : U32)))

def mat.ctr.hit(+ari: U32, +ml: U32, +cl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  match ari:
    case 0:
      (h, rh, rl) = r
      (h, nx, it, rh, rl)
    case n:
      (h, rh, rl) = r
      mat.ctr.h1(n, ml, cl, nx, it, rh, rl, rd(h, cl))

def mat.ctr.go2(z: Bool, h: Array<U32>, +nx: U32, it: Nat, +ml: U32, +th: U32, +tl: U32) -> R():
  match z:
    case True{}:
      mat.ctr.hit((tg(th) - 13 : U32), ml, tl, nx, it, rd(h, ml))
    case False{}:
      mat.mis.k(ml, th, tl, nx, it, rd(h, (ml + 1 : U32)))

# (λ{#K:h; m} #K{a,b}) -> (h a b)  /  (λ{#K:h; m} #L{..}) -> (m #L{..})
def mat.ctr(h: Array<U32>, +nx: U32, it: Nat, +fh: U32, +fl: U32, +th: U32, +tl: U32) -> R():
  mat.ctr.go2(U32.is_eq(ex(fh), ex(th)), h, nx, 1n+it, fl, th, tl)

def mat.num.go(z: Bool, h: Array<U32>, +nx: U32, it: Nat, +ml: U32, +th: U32, +tl: U32) -> R():
  match z:
    case True{}:
      ret(nx, it, rd(h, ml))
    case False{}:
      mat.mis.k(ml, th, tl, nx, it, rd(h, (ml + 1 : U32)))

# (λ{#a:h; m} #a) -> h  /  (λ{#a:h; m} #b) -> (m #b)
def mat.num(h: Array<U32>, +nx: U32, it: Nat, +fh: U32, +fl: U32, +th: U32, +tl: U32) -> R():
  mat.num.go(U32.is_eq(ex(fh), tl), h, nx, 1n+it, fl, th, tl)

# Interactions: USE
# =================

# (λ{f} &L{a,b}) -> ! F &L = f; &L{(λ{F₀} a), (λ{F₁} b)}
def use.sup.k(+ul: U32, +lab: U32, +sl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, nx, hd(3, lab), ul)
  h = wr(h, (nx + 1 : U32), hd(4, lab), ul)
  h = wr(h, (nx + 2 : U32), hd(32, 0), nx)
  h = wr(h, (nx + 3 : U32), ah, al)
  h = wr(h, (nx + 4 : U32), hd(32, 0), (nx + 1 : U32))
  h = wr(h, (nx + 5 : U32), bh, bl)
  h = wr(h, sl, hd(0, 0), (nx + 2 : U32))
  h = wr(h, (sl + 1 : U32), hd(0, 0), (nx + 4 : U32))
  (h, (nx + 6 : U32), it, hd(5, lab), sl)

def use.sup(h: Array<U32>, +nx: U32, it: Nat, +fl: U32, +th: U32, +tl: U32) -> R():
  use.sup.k(fl, ex(th), tl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (λ{f} ↑x) -> ↑(λ{f} x)
def use.inc(h: Array<U32>, +nx: U32, it: Nat, +fh: U32, +fl: U32, +tl: U32) -> R():
  mat.inc.k(fh, fl, tl, nx, 1n+it, rd(h, tl))

# (λ{f} x) -> (f x)
def use.val.k(+th: U32, +tl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, fh, fl) = r
  h = wr(h, nx, fh, fl)
  h = wr(h, (nx + 1 : U32), th, tl)
  (h, (nx + 2 : U32), it, hd(0, 0), nx)

def use.val(h: Array<U32>, +nx: U32, it: Nat, +fl: U32, +th: U32, +tl: U32) -> R():
  use.val.k(th, tl, nx, 1n+it, rd(h, fl))

# Interactions: DUP
# =================

# ! X &L = name -> X₀ ← name; X₁ ← name  (also DUP-NOD at arity 0)
def dup.nam(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +th: U32, +tl: U32) -> R():
  (wr(h, loc, sub.on(th), tl), nx, 1n+it, th, tl)

def dup.lam.go(z: Bool, +side: U32, +loc: U32, +lab: U32, +ll: U32, +le: U32, +nx: U32, it: Nat, h: Array<U32>, +bh: U32, +bl: U32) -> R():
  match z:
    case True{}:
      h = wr(h, (nx + 2 : U32), bh, bl)
      h = wr(h, nx, hd(3, lab), (nx + 2 : U32))
      h = wr(h, (nx + 1 : U32), hd(4, lab), (nx + 2 : U32))
      cop(side, h, loc, hd(2, le), nx, hd(2, le), (nx + 1 : U32), (nx + 3 : U32), it)
    case False{}:
      h = wr(h, (nx + 4 : U32), bh, bl)
      h = wr(h, nx, hd(3, lab), (nx + 4 : U32))
      h = wr(h, (nx + 1 : U32), hd(4, lab), (nx + 4 : U32))
      h = wr(h, (nx + 2 : U32), hd(1, 0), nx)
      h = wr(h, (nx + 3 : U32), hd(1, 0), (nx + 1 : U32))
      h = wr(h, ll, sub.on(hd(5, lab)), (nx + 2 : U32))
      cop(side, h, loc, hd(2, le), nx, hd(2, le), (nx + 1 : U32), (nx + 5 : U32), it)

def dup.lam.k(+side: U32, +loc: U32, +lab: U32, +ll: U32, +le: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, bh, bl) = r
  dup.lam.go(is.era(le), side, loc, lab, ll, le, nx, it, h, bh, bl)

# ! F &L = λx.f -> F₀ ← λ$x0.G₀; F₁ ← λ$x1.G₁; x ← &L{$x0,$x1}; ! G &L = f
def dup.lam(h: Array<U32>, +nx: U32, it: Nat, +side: U32, +loc: U32, +lab: U32, +th: U32, +tl: U32) -> R():
  dup.lam.k(side, loc, lab, tl, ex(th), nx, 1n+it, rd(h, tl))

def dup.sup.eq(+side: U32, +loc: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  cop(side, h, loc, ah, al, bh, bl, nx, it)

def dup.sup.go(z: Bool, h: Array<U32>, +nx: U32, it: Nat, +side: U32, +loc: U32, +lab: U32, +sab: U32, +sl: U32) -> R():
  match z:
    case True{}:
      dup.sup.eq(side, loc, nx, it, rd2(h, sl, (sl + 1 : U32)))
    case False{}:
      h = wr(h, nx, hd(3, lab), sl)
      h = wr(h, (nx + 1 : U32), hd(3, lab), (sl + 1 : U32))
      h = wr(h, (nx + 2 : U32), hd(4, lab), sl)
      h = wr(h, (nx + 3 : U32), hd(4, lab), (sl + 1 : U32))
      cop(side, h, loc, hd(5, sab), nx, hd(5, sab), (nx + 2 : U32), (nx + 4 : U32), it)

# ! X &L = &R{a,b} -> L == R: X₀ ← a; X₁ ← b
#                  -> else:   X₀ ← &R{A₀,B₀}; X₁ ← &R{A₁,B₁}; ! A &L = a; ! B &L = b
def dup.sup(h: Array<U32>, +nx: U32, it: Nat, +side: U32, +loc: U32, +lab: U32, +th: U32, +tl: U32) -> R():
  dup.sup.go(U32.is_eq(lab, ex(th)), h, nx, 1n+it, side, loc, lab, ex(th), tl)

def dup.nod.fill(k: Nat, h: Array<U32>, +lab: U32, +tl: U32, +blk: U32, +ari: U32, +i: U32) -> Array<U32>:
  match k:
    case 0n:
      h
    case 1n+p:
      h = wr(h, (blk + i : U32), hd(3, lab), (tl + i : U32))
      h = wr(h, (blk + ari + i : U32), hd(4, lab), (tl + i : U32))
      dup.nod.fill(p, h, lab, tl, blk, ari, (i + 1 : U32))

def dup.nod.go(+ari: U32, h: Array<U32>, +nx: U32, it: Nat, +side: U32, +loc: U32, +lab: U32, +th: U32, +tl: U32) -> R():
  match ari:
    case 0:
      (wr(h, loc, sub.on(th), tl), nx, it, th, tl)
    case n:
      h = dup.nod.fill(U32.to_nat(n), h, lab, tl, nx, n, 0)
      +t = hd(tg(th), ex(th))
      cop(side, h, loc, t, nx, t, (nx + n : U32), (nx + n + n : U32), it)

# ! X &L = T{a,b,..} -> ! A &L = a; ! B &L = b; ..; X₀ ← T{A₀,B₀,..}; X₁ ← T{A₁,B₁,..}
def dup.nod(h: Array<U32>, +nx: U32, it: Nat, +side: U32, +loc: U32, +lab: U32, +th: U32, +tl: U32) -> R():
  dup.nod.go(arity(tg(th)), h, nx, 1n+it, side, loc, lab, th, tl)

# Interactions: OP2
# =================

# (&L{a,b} op y) -> ! Y &L = y; &L{(a op Y₀), (b op Y₁)}
def op2.sup.k(+loc: U32, +opr: U32, +lab: U32, +sl: U32, +yh: U32, +yl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, nx, yh, yl)
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 1 : U32), bh, bl)
  h = wr(h, (nx + 2 : U32), hd(4, lab), nx)
  h = wr(h, sl, hd(33, opr), loc)
  h = wr(h, (sl + 1 : U32), hd(33, opr), (nx + 1 : U32))
  (h, (nx + 3 : U32), it, hd(5, lab), sl)

def op2.sup(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +opr: U32, +th: U32, +tl: U32, +yh: U32, +yl: U32) -> R():
  op2.sup.k(loc, opr, ex(th), tl, yh, yl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (↑x op y) -> ↑(x op y)
def op2.incx.k(+opr: U32, +il: U32, +yh: U32, +yl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, xh, xl) = r
  h = wr(h, nx, xh, xl)
  h = wr(h, (nx + 1 : U32), yh, yl)
  h = wr(h, il, hd(33, opr), nx)
  (h, (nx + 2 : U32), it, hd(41, 0), il)

def op2.incx(h: Array<U32>, +nx: U32, it: Nat, +opr: U32, +tl: U32, +yh: U32, +yl: U32) -> R():
  op2.incx.k(opr, tl, yh, yl, nx, 1n+it, rd(h, tl))

# (#n op &L{a,b}) -> &L{(#n op a), (#n op b)}
def op2.nsup.k(+opr: U32, +x: U32, +lab: U32, +sl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, nx, hd(30, 0), x)
  h = wr(h, (nx + 1 : U32), ah, al)
  h = wr(h, (nx + 2 : U32), hd(30, 0), x)
  h = wr(h, (nx + 3 : U32), bh, bl)
  h = wr(h, sl, hd(33, opr), nx)
  h = wr(h, (sl + 1 : U32), hd(33, opr), (nx + 2 : U32))
  (h, (nx + 4 : U32), it, hd(5, lab), sl)

def op2.nsup(h: Array<U32>, +nx: U32, it: Nat, +opr: U32, +x: U32, +th: U32, +tl: U32) -> R():
  op2.nsup.k(opr, x, ex(th), tl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (#n op ↑y) -> ↑(#n op y)
def op2.incy.k(+opr: U32, +x: U32, +il: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, yh, yl) = r
  h = wr(h, nx, hd(30, 0), x)
  h = wr(h, (nx + 1 : U32), yh, yl)
  h = wr(h, il, hd(33, opr), nx)
  (h, (nx + 2 : U32), it, hd(41, 0), il)

def op2.incy(h: Array<U32>, +nx: U32, it: Nat, +opr: U32, +x: U32, +tl: U32) -> R():
  op2.incy.k(opr, x, tl, nx, 1n+it, rd(h, tl))

# a new node of two fields (no interaction)
def new2(h: Array<U32>, +nx: U32, it: Nat, +tag: U32, +ext: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> R():
  h = wr(h, nx, ah, al)
  h = wr(h, (nx + 1 : U32), bh, bl)
  (h, (nx + 2 : U32), it, hd(tag, ext), nx)

# Interactions: EQL
# =================

# (&L{a0,a1} === b) -> ! B &L = b; &L{(a0 === B₀), (a1 === B₁)}
def eql.supl.k(+loc: U32, +lab: U32, +sl: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, a0h, a0l, a1h, a1l) = r
  h = wr(h, nx, bh, bl)
  h = wr(h, loc, a0h, a0l)
  h = wr(h, (loc + 1 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 1 : U32), a1h, a1l)
  h = wr(h, (nx + 2 : U32), hd(4, lab), nx)
  h = wr(h, sl, hd(36, 0), loc)
  h = wr(h, (sl + 1 : U32), hd(36, 0), (nx + 1 : U32))
  (h, (nx + 3 : U32), it, hd(5, lab), sl)

def eql.supl(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +th: U32, +tl: U32, +bh: U32, +bl: U32) -> R():
  eql.supl.k(loc, ex(th), tl, bh, bl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (a === &L{b0,b1}) -> ! A &L = a; &L{(A₀ === b0), (A₁ === b1)}
def eql.supr.k(+loc: U32, +lab: U32, +sl: U32, +ah: U32, +al: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, b0h, b0l, b1h, b1l) = r
  h = wr(h, nx, ah, al)
  h = wr(h, loc, hd(3, lab), nx)
  h = wr(h, (loc + 1 : U32), b0h, b0l)
  h = wr(h, (nx + 1 : U32), hd(4, lab), nx)
  h = wr(h, (nx + 2 : U32), b1h, b1l)
  h = wr(h, sl, hd(36, 0), loc)
  h = wr(h, (sl + 1 : U32), hd(36, 0), (nx + 1 : U32))
  (h, (nx + 3 : U32), it, hd(5, lab), sl)

def eql.supr(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ah: U32, +al: U32, +th: U32, +tl: U32) -> R():
  eql.supr.k(loc, ex(th), tl, ah, al, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (↑a === b) -> ↑(a === b)
def eql.incl.k(+loc: U32, +il: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, ah, al) = r
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), bh, bl)
  h = wr(h, il, hd(36, 0), loc)
  (h, nx, it, hd(41, 0), il)

def eql.incl(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +tl: U32, +bh: U32, +bl: U32) -> R():
  eql.incl.k(loc, tl, bh, bl, nx, 1n+it, rd(h, tl))

# (a === ↑b) -> ↑(a === b)
def eql.incr.k(+loc: U32, +il: U32, +ah: U32, +al: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, bh, bl) = r
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), bh, bl)
  h = wr(h, il, hd(36, 0), loc)
  (h, nx, it, hd(41, 0), il)

def eql.incr(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ah: U32, +al: U32, +tl: U32) -> R():
  eql.incr.k(loc, tl, ah, al, nx, 1n+it, rd(h, tl))

# (λax.af === λbx.bf) -> X fresh; ax ← X; bx ← X; af === bf
def eql.lam.k(+al: U32, +bl: U32, +nam: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, afh, afl, bfh, bfl) = r
  h = wr(h, al, sub.on(hd(9, nam)), 0)
  h = wr(h, bl, sub.on(hd(9, nam)), 0)
  h = wr(h, nx, afh, afl)
  h = wr(h, (nx + 1 : U32), bfh, bfl)
  (h, (nx + 2 : U32), it, hd(36, 0), nx)

# the general arity-n CTR equality: INC(AND(EQL a0 b0, INC(AND(..))))
def eql.ctr.go(k: Nat, +ia: U32, +ib: U32, +i: U32, +ach: U32, +acl: U32, +nx: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> Array<U32> & U32 & U32 & U32:
  match k:
    case 0n:
      (h, ah, al, bh, bl) = r
      (h, nx, ach, acl)
    case 1n+p:
      (h, ah, al, bh, bl) = r
      h = wr(h, nx, ah, al)
      h = wr(h, (nx + 1 : U32), bh, bl)
      h = wr(h, (nx + 2 : U32), ach, acl)
      h = wr(h, (nx + 3 : U32), hd(36, 0), nx)
      h = wr(h, (nx + 4 : U32), hd(41, 0), (nx + 2 : U32))
      eql.ctr.go(p, ia, ib, (i - 1 : U32), hd(37, 0), (nx + 3 : U32), (nx + 5 : U32), rd2(h, (ia + i - 1 : U32), (ib + i - 1 : U32)))

# field 0 goes in the EQL node itself, then INC(AND(eq0, INC(acc))) and INC
def eql.ctr.last(+loc: U32, it: Nat, r: U32 & U32 & U32 & Array<U32> & U32 & U32 & U32 & U32) -> R():
  (+q, ach, acl, h, a0h, a0l, b0h, b0l) = r
  h = wr(h, loc, a0h, a0l)
  h = wr(h, (loc + 1 : U32), b0h, b0l)
  h = wr(h, q, ach, acl)
  h = wr(h, (q + 1 : U32), hd(36, 0), loc)
  h = wr(h, (q + 2 : U32), hd(41, 0), q)
  h = wr(h, (q + 3 : U32), hd(37, 0), (q + 1 : U32))
  (h, (q + 4 : U32), it, hd(41, 0), (q + 3 : U32))

def eql.ctr.pack(+q: U32, +ach: U32, +acl: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> U32 & U32 & U32 & Array<U32> & U32 & U32 & U32 & U32:
  (h, ah, al, bh, bl) = r
  (q, ach, acl, h, ah, al, bh, bl)

def eql.ctr.pair(+loc: U32, +ia: U32, +ib: U32, it: Nat, r: Array<U32> & U32 & U32 & U32) -> R():
  (h, q, ach, acl) = r
  eql.ctr.last(loc, it, eql.ctr.pack(q, ach, acl, rd2(h, ia, ib)))

def eql.ctr.one(+loc: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), bh, bl)
  h = wr(h, nx, hd(36, 0), loc)
  (h, (nx + 1 : U32), it, hd(41, 0), nx)

def eql.ctr.many(+ar: U32, +loc: U32, +ia: U32, +ib: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, nx, ah, al)
  h = wr(h, (nx + 1 : U32), bh, bl)
  eql.ctr.pair(loc, ia, ib, it, eql.ctr.go(U32.to_nat((ar - 2 : U32)), ia, ib, (ar - 2 : U32), hd(36, 0), nx, (nx + 2 : U32), rd2(h, (ia + ar - 2 : U32), (ib + ar - 2 : U32))))

def eql.ctr.ari(+ar: U32, h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ia: U32, +ib: U32) -> R():
  match ar:
    case 0:
      (h, nx, it, hd(30, 0), 1)
    case 1:
      eql.ctr.one(loc, nx, it, rd2(h, ia, ib))
    case n:
      eql.ctr.many(n, loc, ia, ib, nx, it, rd2(h, (ia + n - 1 : U32), (ib + n - 1 : U32)))

def eql.ctr.go2(z: Bool, h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ah: U32, +al: U32, +bl: U32) -> R():
  match z:
    case False{}:
      (h, nx, it, hd(30, 0), 0)
    case True{}:
      eql.ctr.ari((tg(ah) - 13 : U32), h, nx, it, loc, al, bl)

def eql.ctr(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> R():
  eql.ctr.go2(U32.is_eq(sub.off(ah), sub.off(bh)), h, nx, 1n+it, loc, ah, al, bl)

# (λ{#K:ah;am} === λ{#K:bh;bm}) -> (ah === bh) .&. (am === bm)
def eql.two.k(+loc: U32, +tag: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32) -> R():
  (h, a0h, a0l, a1h, a1l, b0h, b0l, b1h, b1l) = r
  h = wr(h, nx, a0h, a0l)
  h = wr(h, (nx + 1 : U32), b0h, b0l)
  h = wr(h, (nx + 2 : U32), a1h, a1l)
  h = wr(h, (nx + 3 : U32), b1h, b1l)
  h = wr(h, loc, hd(36, 0), nx)
  h = wr(h, (loc + 1 : U32), hd(36, 0), (nx + 2 : U32))
  (h, (nx + 4 : U32), it, hd(tag, 0), loc)

def rd4.k(+ah: U32, +al: U32, +bh: U32, +bl: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32:
  (h, ch, cl, dh, dl) = r
  (h, ah, al, bh, bl, ch, cl, dh, dl)

def rd4.go(+lc: U32, +ld: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32:
  (h, ah, al, bh, bl) = r
  rd4.k(ah, al, bh, bl, rd2(h, lc, ld))

# the words at a, a+1, b, b+1
def rd4(h: Array<U32>, +a: U32, +b: U32) -> Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32:
  rd4.go(b, (b + 1 : U32), rd2(h, a, (a + 1 : U32)))

def eql.mat.go(z: Bool, h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +al: U32, +bl: U32) -> R():
  match z:
    case False{}:
      (h, nx, it, hd(30, 0), 0)
    case True{}:
      eql.two.k(loc, 37, nx, it, rd4(h, al, bl))

def eql.mat(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> R():
  eql.mat.go(U32.is_eq(ex(ah), ex(bh)), h, nx, 1n+it, loc, al, bl)

# (λ{af} === λ{bf}) -> af === bf
def eql.use.k(+loc: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, ah, al, bh, bl) = r
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), bh, bl)
  (h, nx, it, hd(36, 0), loc)

# (^(af ax) === ^(bf bx)) -> (af === bf) .&. (ax === bx)
def eql.dry(h: Array<U32>, +nx: U32, it: Nat, +loc: U32, +al: U32, +bl: U32) -> R():
  eql.two.k(loc, 37, nx, 1n+it, rd4(h, al, bl))

def is.nam(+t: U32) -> Bool:
  U32.is_eq(t, 9) || U32.is_eq(t, 42) || U32.is_eq(t, 43) || U32.is_eq(t, 44)

def is.mat(+t: U32) -> Bool:
  U32.is_eq(t, 12) || U32.is_eq(t, 31)

# Interactions: DSU / DDU
# =======================

# &(&L{x,y}){a,b} -> ! A &L = a; ! B &L = b; &L{&(x){A₀,B₀}, &(y){A₁,B₁}}
# ! X &(&L{x,y}) = v; b -> same shape with DDU nodes (tag)
def dsu.sup.k(+tag: U32, +lab: U32, +sl: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, xh, xl, yh, yl) = r
  h = wr(h, nx, ah, al)
  h = wr(h, (nx + 1 : U32), bh, bl)
  h = wr(h, (nx + 2 : U32), xh, xl)
  h = wr(h, (nx + 3 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 4 : U32), hd(3, lab), (nx + 1 : U32))
  h = wr(h, (nx + 5 : U32), yh, yl)
  h = wr(h, (nx + 6 : U32), hd(4, lab), nx)
  h = wr(h, (nx + 7 : U32), hd(4, lab), (nx + 1 : U32))
  h = wr(h, sl, hd(tag, 0), (nx + 2 : U32))
  h = wr(h, (sl + 1 : U32), hd(tag, 0), (nx + 5 : U32))
  (h, (nx + 8 : U32), it, hd(5, lab), sl)

def dsu.sup(h: Array<U32>, +nx: U32, it: Nat, +tag: U32, +th: U32, +tl: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> R():
  dsu.sup.k(tag, ex(th), tl, ah, al, bh, bl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# &(↑x){a,b} -> ↑(&(x){a,b})   (also DDU-INC with tag 35)
def dsu.inc.k(+tag: U32, +il: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, xh, xl) = r
  h = wr(h, nx, xh, xl)
  h = wr(h, (nx + 1 : U32), ah, al)
  h = wr(h, (nx + 2 : U32), bh, bl)
  h = wr(h, il, hd(tag, 0), nx)
  (h, (nx + 3 : U32), it, hd(41, 0), il)

def dsu.inc(h: Array<U32>, +nx: U32, it: Nat, +tag: U32, +tl: U32, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> R():
  dsu.inc.k(tag, tl, ah, al, bh, bl, nx, 1n+it, rd(h, tl))

# ! X &(#n) = v; b -> ! X &n = v; b(X₀, X₁)
def ddu.num(h: Array<U32>, +nx: U32, it: Nat, +lab: U32, +vh: U32, +vl: U32, +bh: U32, +bl: U32) -> R():
  h = wr(h, nx, vh, vl)
  h = wr(h, (nx + 1 : U32), bh, bl)
  h = wr(h, (nx + 2 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 3 : U32), hd(0, 0), (nx + 1 : U32))
  h = wr(h, (nx + 4 : U32), hd(4, lab), nx)
  (h, (nx + 5 : U32), 1n+it, hd(0, 0), (nx + 3 : U32))

# Interactions: AND / OR
# ======================

# (&L{a0,a1} .&. b) -> ! B &L = b; &L{(a0 .&. B₀), (a1 .&. B₁)}   (OR: tag 38)
def and.sup.k(+tag: U32, +loc: U32, +lab: U32, +sl: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32 & U32 & U32) -> R():
  (h, a0h, a0l, a1h, a1l) = r
  h = wr(h, nx, bh, bl)
  h = wr(h, loc, a0h, a0l)
  h = wr(h, (loc + 1 : U32), hd(3, lab), nx)
  h = wr(h, (nx + 1 : U32), a1h, a1l)
  h = wr(h, (nx + 2 : U32), hd(4, lab), nx)
  h = wr(h, sl, hd(tag, 0), loc)
  h = wr(h, (sl + 1 : U32), hd(tag, 0), (nx + 1 : U32))
  (h, (nx + 3 : U32), it, hd(5, lab), sl)

def and.sup(h: Array<U32>, +nx: U32, it: Nat, +tag: U32, +loc: U32, +th: U32, +tl: U32, +bh: U32, +bl: U32) -> R():
  and.sup.k(tag, loc, ex(th), tl, bh, bl, nx, 1n+it, rd2(h, tl, (tl + 1 : U32)))

# (↑a .&. b) -> ↑(a .&. b)   (OR: tag 38)
def and.inc.k(+tag: U32, +loc: U32, +il: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, ah, al) = r
  h = wr(h, loc, ah, al)
  h = wr(h, (loc + 1 : U32), bh, bl)
  h = wr(h, il, hd(tag, 0), loc)
  (h, nx, it, hd(41, 0), il)

def and.inc(h: Array<U32>, +nx: U32, it: Nat, +tag: U32, +loc: U32, +tl: U32, +bh: U32, +bl: U32) -> R():
  and.inc.k(tag, loc, tl, bh, bl, nx, 1n+it, rd(h, tl))

# ! ${f, v}; t -> t(λy.λ$x.y, $x)
def uns.k(+nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, bh, bl) = r
  h = wr(h, nx, hd(1, 0), (nx + 1 : U32))
  h = wr(h, (nx + 1 : U32), hd(2, 0), nx)
  h = wr(h, (nx + 2 : U32), bh, bl)
  h = wr(h, (nx + 3 : U32), hd(2, 0), (nx + 1 : U32))
  h = wr(h, (nx + 4 : U32), hd(0, 0), (nx + 2 : U32))
  h = wr(h, (nx + 5 : U32), hd(1, 0), nx)
  (h, (nx + 6 : U32), it, hd(0, 0), (nx + 4 : U32))

# Allocation (ALO): a book term under a bind list
# ===============================================

# one step down the bind list: the next node is val(heap[it + 1]); 0 stays 0
def alo.walk.step(z: Bool, h: Array<U32>, +it: U32) -> Array<U32> & U32 & U32:
  match z:
    case True{}:
      (h, 0, 0)
    case False{}:
      rd(h, (it + 1 : U32))

# the bind list's k-th node (0 = innermost); r = (h, _, node)
def alo.walk(k: Nat, r: Array<U32> & U32 & U32) -> Array<U32> & U32:
  match k:
    case 0n:
      (h, xh, xl) = r
      (h, xl)
    case 1n+p:
      (h, xh, xl0) = r
      +xl = {xl0 : U32}
      alo.walk(p, alo.walk.step(U32.is_zero(xl), h, xl))

def alo.var.fin(z: Bool, +rt: U32, +bh: U32, +bl: U32, +at: U32, +nx: U32, it: Nat, h: Array<U32>) -> R():
  match z:
    case True{}:
      (h, nx, it, hd(tg(bh), ex(bh)), bl)
    case False{}:
      (h, nx, it, rt, at)

# ALO-VAR / ALO-DP0 / ALO-DP1: the found bind, or the book var unchanged
def alo.var.k(+rt: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat, r: Array<U32> & U32) -> R():
  (h, +at) = r
  alo.var.fin(U32.is_zero(at), rt, bh, bl, at, nx, it, h)

def alo.var.go(z: Bool, h: Array<U32>, +rt: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  match z:
    case True{}:
      (h, nx, it, hd(tg(bh), ex(bh)), bl)
    case False{}:
      alo.var.k(rt, bh, bl, nx, it, alo.walk(U32.to_nat((len - bl : U32)), (h, 0, ls)))

# rt: the dynamic word to answer when the bind is found (VAR, DP0 or DP1)
def alo.var(h: Array<U32>, +rt: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  alo.var.go(U32.is_zero(bl) || U32.is_gt(bl, len), h, rt, ls, len, bh, bl, nx, it)

def alo.lam.go(z: Bool, h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  match z:
    case True{}:
      h = wr(h, (nx + 2 : U32), nx, bl)
      h = wr(h, nx, hd(7, (len + 1 : U32)), (nx + 2 : U32))
      h = wr(h, (nx + 1 : U32), hd(30, 0), ls)
      (h, (nx + 3 : U32), it, hd(2, ex(bh)), nx)
    case False{}:
      h = wr(h, al, nx, bl)
      h = wr(h, nx, hd(7, (len + 1 : U32)), al)
      h = wr(h, (nx + 1 : U32), hd(30, 0), ls)
      (h, (nx + 2 : U32), it, hd(2, ex(bh)), nx)

# @{s} λx.f -> x' fresh; λx'.@{x',s}f
def alo.lam(h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  alo.lam.go(U32.is_zero(len), h, al, ls, len, bh, bl, nx, it)

def alo.dup.go(z: Bool, h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  match z:
    case True{}:
      h = wr(h, nx, hd(7, 0), bl)
      h = wr(h, (nx + 1 : U32), hd(30, 0), ls)
      h = wr(h, (nx + 2 : U32), nx, (bl + 1 : U32))
      (h, (nx + 3 : U32), it, hd(7, (len + 1 : U32)), (nx + 2 : U32))
    case False{}:
      h = wr(h, al, ls, bl)
      h = wr(h, nx, hd(7, len), al)
      h = wr(h, (nx + 1 : U32), hd(30, 0), ls)
      h = wr(h, (nx + 2 : U32), nx, (bl + 1 : U32))
      (h, (nx + 3 : U32), it, hd(7, (len + 1 : U32)), (nx + 2 : U32))

# @{s} ! x &L = v; t -> x' fresh; ! x' &L = @{s} v; @{x',s} t
def alo.dup(h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  alo.dup.go(U32.is_zero(len), h, al, ls, len, bl, nx, it)

# fields 1.. of ALO-NOD: each a fresh ALO pair word (len > 0)
def alo.nod.fill(k: Nat, h: Array<U32>, +ls: U32, +len: U32, +bl: U32, +nd: U32, +i: U32, +pw: U32) -> Array<U32>:
  match k:
    case 0n:
      h
    case 1n+p:
      h = wr(h, pw, ls, (bl + i : U32))
      h = wr(h, (nd + i : U32), hd(7, len), pw)
      alo.nod.fill(p, h, ls, len, bl, nd, (i + 1 : U32), (pw + 1 : U32))

# fields of ALO-NOD at len 0: @{}(loc + i), no pair words
def alo.nod.fill0(k: Nat, h: Array<U32>, +bl: U32, +nd: U32, +i: U32) -> Array<U32>:
  match k:
    case 0n:
      h
    case 1n+p:
      h = wr(h, (nd + i : U32), hd(7, 0), (bl + i : U32))
      alo.nod.fill0(p, h, bl, nd, (i + 1 : U32))

def alo.nod.go(+ari: U32, z: Bool, h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  match ari z:
    case 0 _:
      (h, nx, it, bh, bl)
    case n True{}:
      h = alo.nod.fill0(U32.to_nat(n), h, bl, nx, 0)
      (h, (nx + n : U32), it, hd(tg(bh), ex(bh)), nx)
    case n False{}:
      +nd = (nx + n - 1 : U32)
      h = wr(h, al, ls, bl)
      h = wr(h, nd, hd(7, len), al)
      h = alo.nod.fill(U32.to_nat((n - 1 : U32)), h, ls, len, bl, nd, 1, nx)
      (h, (nd + n : U32), it, hd(tg(bh), ex(bh)), nd)

# @{s} T{a,b,...} -> T{@{s}a, @{s}b, ...}
def alo.nod(h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  alo.nod.go(arity(tg(bh)), U32.is_zero(len), h, al, ls, len, bh, bl, nx, it)

# one ALO step on the book word (bh, bl)
def alo.book(+t: U32, h: Array<U32>, +al: U32, +ls: U32, +len: U32, +bh: U32, +bl: U32, +nx: U32, it: Nat) -> R():
  match t:
    case 1:
      alo.var(h, hd(1, 0), ls, len, bh, bl, nx, it)
    case 42:
      alo.var(h, hd(1, 0), ls, len, bh, bl, nx, it)
    case 3:
      alo.var(h, hd(3, ex(bh)), ls, len, bh, bl, nx, it)
    case 43:
      alo.var(h, hd(3, ex(bh)), ls, len, bh, bl, nx, it)
    case 4:
      alo.var(h, hd(4, ex(bh)), ls, len, bh, bl, nx, it)
    case 44:
      alo.var(h, hd(4, ex(bh)), ls, len, bh, bl, nx, it)
    case 2:
      alo.lam(h, al, ls, len, bh, bl, nx, it)
    case 6:
      alo.dup(h, al, ls, len, bl, nx, it)
    case 9:
      (h, nx, it, bh, bl)
    case 30:
      (h, nx, it, bh, bl)
    case 8:
      (h, nx, it, bh, bl)
    case 11:
      (h, nx, it, bh, bl)
    case 40:
      (h, nx, it, bh, bl)
    case x:
      alo.nod(h, al, ls, len, bh, bl, nx, it)

def alo.k2(+al: U32, +ls: U32, +len: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, +bh, bl) = r
  alo.book(tg(bh), h, al, ls, len, bh, bl, nx, it)

def alo.k1(+al: U32, +len: U32, +nx: U32, it: Nat, r: Array<U32> & U32 & U32) -> R():
  (h, ls, tm0) = r
  +tm = {tm0 : U32}
  alo.k2(al, ls, len, nx, it, rd(h, tm))

def alo.go(+len: U32, h: Array<U32>, +tl: U32, +nx: U32, it: Nat) -> R():
  match len:
    case 0:
      alo.k2(0, 0, 0, nx, it, rd(h, tl))
    case n:
      alo.k1(tl, n, nx, it, rd(h, tl))

# The machine: enter
# ==================

def push(s: Array<U32>, +sp: U32, +hi: U32, +lo: U32) -> Array<U32>:
  wr(s, sp, hi, lo)

def e.var.go(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +ch: U32, +cl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, er, 0, sub.off(ch), cl, hl)
    case False{}:
      (h, s, sp, nx, it, fr, er, 1, th, tl, hl)

# VAR: a substituted cell continues there, a free one is a value
def e.var(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, +ch, cl) = r
  e.var.go(is.sub(ch), h, s, sp, nx, it, fr, er, hl, th, tl, ch, cl)

def e.dup.go(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +ch: U32, +cl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, er, 0, sub.off(ch), cl, hl)
    case False{}:
      (h, push(s, sp, th, tl), (sp + 1 : U32), nx, it, fr, er, 0, ch, cl, hl)

# DP0/DP1: a substituted cell continues there, else push and enter the expr
def e.dup(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, +ch, cl) = r
  e.dup.go(is.sub(ch), h, s, sp, nx, it, fr, er, hl, th, tl, ch, cl)

# APP/OP2/EQL/AND/OR/DSU/DDU: push, enter field 0
def e.push(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, xh, xl) = r
  (h, push(s, sp, th, tl), (sp + 1 : U32), nx, it, fr, er, 0, xh, xl, hl)

def e.ref.go(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +bl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, er, 1, th, tl, hl)
    case False{}:
      (h, s, sp, nx, it, fr, er, 0, hd(7, 0), bl, hl)

# REF: its book entry (word 1 + id) holds the def's book loc, 0 if none
def e.ref(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, bh, bl0) = r
  +bl = {bl0 : U32}
  e.ref.go(U32.is_zero(bl), h, s, sp, nx, it, fr, er, hl, th, tl, bl)

def e.tag(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32) -> W():
  match t:
    case 1:
      e.var(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 3:
      e.dup(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 4:
      e.dup(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 0:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 6:
      k.ent(s, sp, fr, er, hl, ret(nx, it, rd(h, (tl + 1 : U32))))
    case 39:
      k.ent(s, sp, fr, er, hl, uns.k(nx, 1n+it, rd(h, tl)))
    case 8:
      e.ref(s, sp, nx, it, fr, er, hl, th, tl, rd(h, (ex(th) + 1 : U32)))
    case 7:
      k.ent(s, sp, fr, er, hl, alo.go(ex(th), h, tl, nx, it))
    case 33:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 36:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 37:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 38:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 34:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case 35:
      e.push(s, sp, nx, it, fr, er, hl, th, tl, rd(h, tl))
    case x:
      (h, s, sp, nx, it, fr, er, 1, th, tl, hl)

# The machine: apply
# ==================

def a.app.other(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, 2, 2, th, tl, hl)
    case False{}:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

# APP frame (□ x): the function is in hand
def a.app.go(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, +ah: U32, +al: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 9:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, hd(10, 0), fl, hl)
    case 42:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, hd(10, 0), fl, hl)
    case 43:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, hd(10, 0), fl, hl)
    case 44:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, hd(10, 0), fl, hl)
    case 10:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, hd(10, 0), fl, hl)
    case 2:
      k.ent(s, sp, fr, er, hl, app.lam(h, nx, it, th, tl, ah, al))
    case 5:
      k.app(s, sp, fr, er, hl, app.sup(h, nx, it, fl, th, tl, ah, al))
    case 41:
      k.app(s, sp, fr, er, hl, app.inc(h, nx, it, fl, th, tl))
    case 12:
      (h, push(s, sp, th, tl), (sp + 1 : U32), nx, it, fr, er, 0, ah, al, hl)
    case 31:
      (h, push(s, sp, th, tl), (sp + 1 : U32), nx, it, fr, er, 0, ah, al, hl)
    case 32:
      (h, push(s, sp, th, tl), (sp + 1 : U32), nx, it, fr, er, 0, ah, al, hl)
    case 30:
      (h, s, sp, nx, it, fr, 1, 2, th, tl, hl)
    case x:
      a.app.other(is.ctr(x), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)

def a.app(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, ah, al) = r
  a.app.go(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl, ah, al)

def a.mat.other(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, mat.ctr(h, nx, it, fh, fl, th, tl))
    case False{}:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 0, 0, fh, fl, th, tl))

# MAT/SWI frame (mat □): the argument is in hand
def a.mat(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 5:
      k.app(s, sp, fr, er, hl, mat.sup(h, nx, it, fh, fl, th, tl))
    case 41:
      k.app(s, sp, fr, er, hl, mat.inc(h, nx, it, fh, fl, tl))
    case 30:
      k.ent(s, sp, fr, er, hl, mat.num(h, nx, it, fh, fl, th, tl))
    case 9:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 10, 0, fh, fl, th, tl))
    case 42:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 10, 0, fh, fl, th, tl))
    case 43:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 10, 0, fh, fl, th, tl))
    case 44:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 10, 0, fh, fl, th, tl))
    case 10:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 10, 0, fh, fl, th, tl))
    case x:
      a.mat.other(is.ctr(x), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)

# USE frame (λ{f} □)
def a.use(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 5:
      k.app(s, sp, fr, er, hl, use.sup(h, nx, it, fl, th, tl))
    case 41:
      k.app(s, sp, fr, er, hl, use.inc(h, nx, it, fh, fl, tl))
    case x:
      k.ent(s, sp, fr, er, hl, use.val(h, nx, it, fl, th, tl))

def a.dup.other(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case False{}:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

# DP0/DP1 frame: the dup's expr is in hand
def a.dup(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match t:
    case 9:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 42:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 43:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 44:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 11:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 40:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 30:
      k.app(s, sp, fr, er, hl, dup.nam(h, nx, it, fl, th, tl))
    case 2:
      k.app(s, sp, fr, er, hl, dup.lam(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 5:
      k.ent(s, sp, fr, er, hl, dup.sup(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 10:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 12:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 31:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 32:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 41:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 33:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 34:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case 35:
      k.ent(s, sp, fr, er, hl, dup.nod(h, nx, it, (tg(fh) - 3 : U32), fl, ex(fh), th, tl))
    case x:
      a.dup.other(is.ctr(x), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)

def a.op2.num(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +opr: U32, +x: U32, +yh: U32, +yl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, 1n+it, fr, er, 1, hd(30, 0), op2(opr, x, yl), hl)
    case False{}:
      (h, push(s, sp, hd(67, opr), x), (sp + 1 : U32), nx, it, fr, er, 0, yh, yl, hl)

# OP2 frame (□ op y): x is in hand
def a.op2.go(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, +yh: U32, +yl: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 30:
      a.op2.num(U32.is_eq(tg(yh), 30), h, s, sp, nx, it, fr, er, hl, ex(fh), tl, yh, yl)
    case 5:
      k.app(s, sp, fr, er, hl, op2.sup(h, nx, it, fl, ex(fh), th, tl, yh, yl))
    case 41:
      k.app(s, sp, fr, er, hl, op2.incx(h, nx, it, ex(fh), tl, yh, yl))
    case x:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

def a.op2(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, yh, yl) = r
  a.op2.go(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl, yh, yl)

# F_OP2_NUM frame (#x op □): y is in hand
def a.op2n(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +opr: U32, +x: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 30:
      (h, s, sp, nx, 1n+it, fr, er, 1, hd(30, 0), op2(opr, x, tl), hl)
    case 5:
      k.app(s, sp, fr, er, hl, op2.nsup(h, nx, it, opr, x, th, tl))
    case 41:
      k.app(s, sp, fr, er, hl, op2.incy(h, nx, it, opr, x, tl))
    case y:
      k.app(s, sp, fr, er, hl, new2(h, nx, it, 33, opr, hd(30, 0), x, th, tl))

# EQL frame (□ === b): a is in hand
def a.eql.go(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, +bh: U32, +bl: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 40:
      k.app(s, sp, fr, er, hl, num(h, nx, it, 1))
    case 5:
      k.app(s, sp, fr, er, hl, eql.supl(h, nx, it, fl, th, tl, bh, bl))
    case 41:
      k.app(s, sp, fr, er, hl, eql.incl(h, nx, it, fl, tl, bh, bl))
    case x:
      (wr(h, fl, th, tl), push(s, sp, hd(69, 0), fl), (sp + 1 : U32), nx, it, fr, er, 0, bh, bl, hl)

def a.eql(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, bh, bl) = r
  a.eql.go(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl, bh, bl)

def a.eqr.c8(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +tl: U32, +loc: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, eql.dry(h, nx, it, loc, al, tl))
    case False{}:
      k.app(s, sp, fr, er, hl, num(h, nx, it, 0))

def a.eqr.c7(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.app(s, sp, fr, er, hl, num(h, nx, it, b2u(U32.is_eq(ah, th) && U32.is_eq(al, tl))))
    case False{}:
      a.eqr.c8(U32.is_eq(at, 10) && U32.is_eq(bt, 10), h, s, sp, nx, it, fr, er, hl, tl, loc, al)

def a.eqr.c6(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, eql.use.k(loc, nx, 1n+it, rd2(h, al, tl)))
    case False{}:
      a.eqr.c7(is.nam(at) && is.nam(bt), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr.c5(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, eql.mat(h, nx, it, loc, ah, al, th, tl))
    case False{}:
      a.eqr.c6(U32.is_eq(at, 32) && U32.is_eq(bt, 32), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr.c4(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, fr, er, hl, eql.ctr(h, nx, it, loc, ah, al, th, tl))
    case False{}:
      a.eqr.c5(is.mat(at) && is.mat(bt), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr.c3(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.ent(s, sp, (fr + 1 : U32), er, hl, eql.lam.k(al, tl, fr, nx, 1n+it, rd2(h, al, tl)))
    case False{}:
      a.eqr.c4(is.ctr(at) && is.ctr(bt), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr.c2(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.app(s, sp, fr, er, hl, num(h, nx, it, b2u(U32.is_eq(al, tl))))
    case False{}:
      a.eqr.c3(U32.is_eq(at, 2) && U32.is_eq(bt, 2), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr.c1(z: Bool, +at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match z:
    case True{}:
      k.app(s, sp, fr, er, hl, num(h, nx, it, 1))
    case False{}:
      a.eqr.c2(U32.is_eq(at, 30) && U32.is_eq(bt, 30), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

# both sides are WHNF: compare by tags
def a.eqr.cmp(+at: U32, +bt: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  a.eqr.c1(U32.is_eq(at, 40) || U32.is_eq(bt, 40), at, bt, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

# F_EQL_R frame (a === □): b is in hand, a's WHNF waits in loc + 0
def a.eqr.go(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, +ah: U32, +al: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 40:
      k.app(s, sp, fr, er, hl, num(h, nx, it, 1))
    case 5:
      k.app(s, sp, fr, er, hl, eql.supr(h, nx, it, loc, ah, al, th, tl))
    case 41:
      k.app(s, sp, fr, er, hl, eql.incr(h, nx, it, loc, ah, al, tl))
    case x:
      a.eqr.cmp(tg(ah), x, h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

def a.eqr(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +loc: U32, r: Array<U32> & U32 & U32) -> W():
  (h, ah, al) = r
  a.eqr.go(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, loc, ah, al)

# DSU frame &(□){a,b} and DDU frame ! X &(□) = v; b: the label is in hand
def a.dsu.go(+t: U32, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> W():
  match t:
    case 11:
      (h, ah, al, bh, bl) = r
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 30:
      (h, ah, al, bh, bl) = r
      k.app(s, sp, fr, er, hl, new2(h, nx, 1n+it, 5, tl, ah, al, bh, bl))
    case 5:
      (h, ah, al, bh, bl) = r
      k.app(s, sp, fr, er, hl, dsu.sup(h, nx, it, 34, th, tl, ah, al, bh, bl))
    case 41:
      (h, ah, al, bh, bl) = r
      k.app(s, sp, fr, er, hl, dsu.inc(h, nx, it, 34, tl, ah, al, bh, bl))
    case x:
      (h, ah, al, bh, bl) = r
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

def a.ddu.go(+t: U32, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32 & U32 & U32) -> W():
  match t:
    case 11:
      (h, vh, vl, bh, bl) = r
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 30:
      (h, vh, vl, bh, bl) = r
      k.ent(s, sp, fr, er, hl, ddu.num(h, nx, it, tl, vh, vl, bh, bl))
    case 5:
      (h, vh, vl, bh, bl) = r
      k.app(s, sp, fr, er, hl, dsu.sup(h, nx, it, 35, th, tl, vh, vl, bh, bl))
    case 41:
      (h, vh, vl, bh, bl) = r
      k.app(s, sp, fr, er, hl, dsu.inc(h, nx, it, 35, tl, vh, vl, bh, bl))
    case x:
      (h, vh, vl, bh, bl) = r
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

# AND: #0 -> #0, #n -> b;  OR: #0 -> b, #n -> #1
def a.and.num(+t: U32, z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +bh: U32, +bl: U32) -> W():
  match t z:
    case 37 True{}:
      (h, s, sp, nx, 1n+it, fr, er, 1, hd(30, 0), 0, hl)
    case 37 False{}:
      (h, s, sp, nx, 1n+it, fr, er, 0, bh, bl, hl)
    case x True{}:
      (h, s, sp, nx, 1n+it, fr, er, 0, bh, bl, hl)
    case x False{}:
      (h, s, sp, nx, 1n+it, fr, er, 1, hd(30, 0), 1, hl)

# AND / OR frames (□ .&. b), (□ .|. b): a is in hand
def a.and.go(+t: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, +bh: U32, +bl: U32) -> W():
  match t:
    case 11:
      k.app(s, sp, fr, er, hl, era(h, nx, it))
    case 5:
      k.app(s, sp, fr, er, hl, and.sup(h, nx, it, tg(fh), fl, th, tl, bh, bl))
    case 41:
      k.app(s, sp, fr, er, hl, and.inc(h, nx, it, tg(fh), fl, tl, bh, bl))
    case 30:
      a.and.num(tg(fh), U32.is_zero(tl), h, s, sp, nx, it, fr, er, hl, bh, bl)
    case x:
      (wr(h, fl, th, tl), s, sp, nx, it, fr, er, 1, fh, fl, hl)

def a.and(s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32, r: Array<U32> & U32 & U32) -> W():
  (h, bh, bl) = r
  a.and.go(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl, bh, bl)

# dispatch on the frame's tag
def a.frame(+ft: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, +fh: U32, +fl: U32) -> W():
  match ft:
    case 0:
      a.app(s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd(h, (fl + 1 : U32)))
    case 12:
      a.mat(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)
    case 31:
      a.mat(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)
    case 32:
      a.use(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)
    case 3:
      a.dup(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)
    case 4:
      a.dup(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)
    case 33:
      a.op2(s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd(h, (fl + 1 : U32)))
    case 67:
      a.op2n(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl, ex(fh), fl)
    case 36:
      a.eql(s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd(h, (fl + 1 : U32)))
    case 69:
      a.eqr(s, sp, nx, it, fr, er, hl, th, tl, fl, rd(h, fl))
    case 34:
      a.dsu.go(tg(th), s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd2(h, (fl + 1 : U32), (fl + 2 : U32)))
    case 35:
      a.ddu.go(tg(th), s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd2(h, (fl + 1 : U32), (fl + 2 : U32)))
    case 37:
      a.and(s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd(h, (fl + 1 : U32)))
    case 38:
      a.and(s, sp, nx, it, fr, er, hl, th, tl, fh, fl, rd(h, (fl + 1 : U32)))
    case x:
      (h, s, sp, nx, it, fr, er, 1, th, tl, hl)

def a.pop.k(h: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32, r: Array<U32> & U32 & U32) -> W():
  (s, +fh, fl) = r
  a.frame(tg(fh), h, s, sp, nx, it, fr, er, hl, th, tl, fh, fl)

def a.pop(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, er, 2, th, tl, hl)
    case False{}:
      a.pop.k(h, (sp - 1 : U32), nx, it, fr, er, hl, th, tl, rd(s, (sp - 1 : U32)))

# The machine
# ===========

def step.oom(z: Bool, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32) -> W():
  match z:
    case True{}:
      (h, s, sp, nx, it, fr, 3, 2, th, tl, hl)
    case False{}:
      (h, s, sp, nx, it, fr, 4, 2, th, tl, hl)

def step.md(+md: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32) -> W():
  match md:
    case 0:
      e.tag(tg(th), h, s, sp, nx, it, fr, er, hl, th, tl)
    case x:
      a.pop(U32.is_zero(sp), h, s, sp, nx, it, fr, er, hl, th, tl)

# guards: the heap's last usable word and the stack's capacity
def step.ok(z: Bool, +md: U32, h: Array<U32>, s: Array<U32>, +sp: U32, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +th: U32, +tl: U32) -> W():
  match z:
    case False{}:
      step.oom(U32.is_ge(nx, hl), h, s, sp, nx, it, fr, er, hl, th, tl)
    case True{}:
      step.md(md, h, s, sp, nx, it, fr, er, hl, th, tl)

def wnf.go(fuel: Nat, w: W()) -> W():
  match fuel:
    case 0n:
      (h, s, sp, nx, it, fr, er, md, th, tl, hl) = w
      (h, s, sp, nx, it, fr, 5, 2, th, tl, hl)
    case 1n+p:
      match w:
        case (h, s, sp, nx, it, fr, er, 2, th, tl, hl):
          (h, s, sp, nx, it, fr, er, 2, th, tl, hl)
        case (h, s, sp0, nx0, it, fr, er, md, th, tl, hl0):
          +sp = {sp0 : U32}
          +nx = {nx0 : U32}
          +hl = {hl0 : U32}
          wnf.go(p, step.ok(U32.is_lt(nx, hl) && U32.is_lt(sp, 33554400), md, h, s, sp, nx, it, fr, er, hl, th, tl))

def wnf.fuel() -> Nat:
  Nat.mul(4294967295n, 65535n)

def wnf.out(w: W()) -> S() & U32 & U32:
  (h, s, sp, nx, it, fr, er, md, th, tl, hl) = w
  ((h, s, nx, it, fr, er, hl), th, tl)

# wnf: the weak normal form of (th, tl); the stack is empty between calls
def wnf(m: S(), +th: U32, +tl: U32) -> S() & U32 & U32:
  (h, s, nx, it, fr, er, hl) = m
  wnf.out(wnf.go(wnf.fuel(), (h, s, 0, nx, it, fr, er, 0, th, tl, hl)))

# is this tag already a value (wnf_at's short-cut list)?
def is.val(+t: U32) -> Bool:
  match t:
    case 9:
      True{}
    case 42:
      True{}
    case 43:
      True{}
    case 44:
      True{}
    case 10:
      True{}
    case 11:
      True{}
    case 5:
      True{}
    case 2:
      True{}
    case 30:
      True{}
    case 12:
      True{}
    case 31:
      True{}
    case 32:
      True{}
    case 41:
      True{}
    case x:
      is.ctr(x)

def wnf.at.put(z: Bool, h: Array<U32>, +loc: U32, +th: U32, +tl: U32) -> Array<U32>:
  match z:
    case True{}:
      h
    case False{}:
      wr(h, loc, th, tl)

def wnf.at.fin(+loc: U32, +ch: U32, +cl: U32, r: S() & U32 & U32) -> S() & U32 & U32:
  ((h, s, nx, it, fr, er, hl), th0, tl0) = r
  +th = {th0 : U32}
  +tl = {tl0 : U32}
  ((wnf.at.put(U32.is_eq(th, ch) && U32.is_eq(tl, cl), h, loc, th, tl), s, nx, it, fr, er, hl), th, tl)

def wnf.at.go(z: Bool, s: Array<U32>, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +loc: U32, h: Array<U32>, +ch: U32, +cl: U32) -> S() & U32 & U32:
  match z:
    case True{}:
      ((h, s, nx, it, fr, er, hl), ch, cl)
    case False{}:
      wnf.at.fin(loc, ch, cl, wnf((h, s, nx, it, fr, er, hl), ch, cl))

def wnf.at.k(s: Array<U32>, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, +loc: U32, r: Array<U32> & U32 & U32) -> S() & U32 & U32:
  (h, +ch, cl) = r
  wnf.at.go(is.val(tg(ch)), s, nx, it, fr, er, hl, loc, h, ch, cl)

# wnf_at: reduce the word at loc in place
def wnf.at(m: S(), +loc: U32) -> S() & U32 & U32:
  (h, s, nx, it, fr, er, hl) = m
  wnf.at.k(s, nx, it, fr, er, hl, loc, rd(h, loc))
