import Base

# hvm5bis: Tm, the static (book) terms HVM4's parser builds, as a tree.
#
# HVM4 (src/hvm.c, Parse section) writes a book term straight into its
# heap: each word is TAG | EXT | VAL, a node's VAL is the location of
# its fields, a variable's VAL is its binder's de Bruijn level (BJV,
# BJ0, BJ1). hvm5bis parses into this tree instead, runs HVM4's two
# parse-time passes on it (count_uses, auto-dup), and only then lays it
# out in the heap. Heap locations never reach the output (the printer
# names binders by depth or by first sight), so the layout may differ
# from HVM4's while every word means the same.
#
#   Tl{tag, ext, val}   a word with no fields (VAR-like, NUM, REF, ERA..)
#   Tb{tag, ext, kids}  a word over its fields; kids is a Tn/Tc list
#   Tn{} / Tc{h, t}     the field list
#
# Tags (as in hvm.c): APP 0, LAM 2, SUP 5, DUP 6, REF 8, NAM 9, DRY 10,
# ERA 11, MAT 12, C00..C16 13..29, NUM 30, SWI 31, USE 32, OP2 33,
# DSU 34, DDU 35, EQL 36, AND 37, OR 38, UNS 39, ANY 40, INC 41,
# BJV 42, BJ0 43, BJ1 44.

type Tm is Data:
  Tl{tag: U32, ext: U32, val: U32}
  Tb{tag: U32, ext: U32, kids: Tm}
  Tn{}
  Tc{head: Tm, tail: Tm}

# Words
# =====

def tm.hd(+tag: U32, +ext: U32) -> U32:
  U32.or(U32.shln(tag, 24n), U32.and(ext, 16777215))

def tm.b2u(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

# Builders
# ========

def tm.num(+n: U32) -> Tm:
  Tl{30, 0, n}

def tm.era() -> Tm:
  Tl{11, 0, 0}

def tm.any() -> Tm:
  Tl{40, 0, 0}

def tm.ref(+nam: U32) -> Tm:
  Tl{8, nam, 0}

def tm.nam(+nam: U32) -> Tm:
  Tl{9, nam, 0}

def tm.bjv(+lvl: U32) -> Tm:
  Tl{42, 0, lvl}

def tm.one(+tag: U32, +ext: U32, a: Tm) -> Tm:
  Tb{tag, ext, Tc{a, Tn{}}}

def tm.two(+tag: U32, +ext: U32, a: Tm, b: Tm) -> Tm:
  Tb{tag, ext, Tc{a, Tc{b, Tn{}}}}

def tm.three(+tag: U32, +ext: U32, a: Tm, b: Tm, c: Tm) -> Tm:
  Tb{tag, ext, Tc{a, Tc{b, Tc{c, Tn{}}}}}

def tm.lam(+ext: U32, b: Tm) -> Tm:
  tm.one(2, ext, b)

def tm.app(f: Tm, x: Tm) -> Tm:
  tm.two(0, 0, f, x)

def tm.sup(+lab: U32, a: Tm, b: Tm) -> Tm:
  tm.two(5, lab, a, b)

def tm.dup(+lab: U32, v: Tm, b: Tm) -> Tm:
  tm.two(6, lab, v, b)

def tm.use(f: Tm) -> Tm:
  tm.one(32, 0, f)

def tm.inc(x: Tm) -> Tm:
  tm.one(41, 0, x)

def tm.uns(b: Tm) -> Tm:
  tm.one(39, 0, b)

def tm.dsu(l: Tm, a: Tm, b: Tm) -> Tm:
  tm.three(34, 0, l, a, b)

def tm.ddu(l: Tm, v: Tm, b: Tm) -> Tm:
  tm.three(35, 0, l, v, b)

def tm.op2(+op: U32, a: Tm, b: Tm) -> Tm:
  tm.two(33, op, a, b)

# the length of a field list
def tm.len(t: Tm) -> U32:
  match t:
    case Tc{h, r}:
      (1 + tm.len(r) : U32)
    case x:
      0

# a constructor over a field list (arity 0 is a leaf word, C00)
def tm.ctr.go(+n: U32, +nam: U32, kids: Tm) -> Tm:
  match n:
    case 0:
      Tl{13, nam, 0}
    case k:
      Tb{(13 + k : U32), nam, kids}

def tm.ctr(+nam: U32, +kids: Tm) -> Tm:
  tm.ctr.go(tm.len(kids), nam, kids)

# count_uses: how many leaves are the variable (tgt, lvl[, ext])
def tm.hit(+tag: U32, +e: U32, +val: U32, +lvl: U32, +tgt: U32, +ext: U32) -> Bool:
  U32.is_eq(tag, tgt) && U32.is_eq(val, lvl) && (U32.is_eq(tgt, 42) || U32.is_eq(e, ext))

def tm.uses(t: Tm, +lvl: U32, +tgt: U32, +ext: U32) -> U32:
  match t:
    case Tl{+tag, +e, +val}:
      tm.b2u(tm.hit(tag, e, val, lvl, tgt, ext))
    case Tb{tag, e, kids}:
      tm.uses(kids, lvl, tgt, ext)
    case Tn{}:
      0
    case Tc{h, r}:
      (tm.uses(h, lvl, tgt, ext) + tm.uses(r, lvl, tgt, ext) : U32)

def tm.is.var(+t: U32) -> Bool:
  U32.is_eq(t, 42) || U32.is_eq(t, 43) || U32.is_eq(t, 44)

def tm.adup.mk(lt: Bool, +use: U32, +n: U32, +lab: U32, +base: U32) -> Tm:
  match lt:
    case True{}:
      Tl{43, (lab + use : U32), (base + 1 + use : U32)}
    case False{}:
      Tl{44, (lab + n - 1 : U32), (base + n : U32)}

def tm.adup.sh(sh: Bool, +tag: U32, +e: U32, +val: U32, +n: U32) -> Tm:
  match sh:
    case True{}:
      Tl{tag, e, (val + n : U32)}
    case False{}:
      Tl{tag, e, val}

# auto_dup_go on one leaf: the use-th occurrence of the target becomes a
# BJ0 of the chain's use-th dup (the last one a BJ1); outer refs shift
def tm.adup.leaf(hit: Bool, +tag: U32, +e: U32, +val: U32, +use: U32, +n: U32, +lab: U32, +base: U32) -> Tm:
  match hit:
    case True{}:
      tm.adup.mk(U32.is_lt(use, n), use, n, lab, base)
    case False{}:
      tm.adup.sh(tm.is.var(tag) && U32.is_gt(val, base), tag, e, val, n)

# auto_dup_go over a term; `use` is the number of targets seen before t
def tm.adup(t: Tm, +lvl: U32, +base: U32, +use: U32, +n: U32, +lab: U32, +tgt: U32, +ext: U32) -> Tm:
  match t:
    case Tl{+tag, +e, +val}:
      tm.adup.leaf(tm.hit(tag, e, val, lvl, tgt, ext), tag, e, val, use, n, lab, base)
    case Tb{tag, e, kids}:
      Tb{tag, e, tm.adup(kids, lvl, base, use, n, lab, tgt, ext)}
    case Tn{}:
      Tn{}
    case Tc{+h, r}:
      Tc{tm.adup(h, lvl, base, use, n, lab, tgt, ext), tm.adup(r, lvl, base, (use + tm.uses(h, lvl, tgt, ext) : U32), n, lab, tgt, ext)}

def tm.chain.v(+i: U32, +lvl: U32, +base: U32, +lab: U32, +tgt: U32, +ext: U32) -> Tm:
  match i:
    case 0:
      Tl{tgt, ext, lvl}
    case j:
      Tl{44, (lab + j - 1 : U32), (base + j : U32)}

# the dup chain over the rewritten body: !d0&=x; !d1&=d0₁; ... body
def tm.chain(k: Nat, +i: U32, +lvl: U32, +base: U32, +lab: U32, +tgt: U32, +ext: U32, body: Tm) -> Tm:
  match k:
    case 0n:
      body
    case 1n+p:
      tm.chain(p, (i - 1 : U32), lvl, base, lab, tgt, ext, tm.dup((lab + i : U32), tm.chain.v(i, lvl, base, lab, tgt, ext), body))

# parse_auto_dup's rewrite with n = uses - 1 > 0 and labels lab..lab+n-1:
# the body's fields are walked (the body word itself is not a target)
def tm.adup.body(t: Tm, +lvl: U32, +base: U32, +n: U32, +lab: U32, +tgt: U32, +ext: U32) -> Tm:
  match t:
    case Tb{tag, e, kids}:
      Tb{tag, e, tm.adup(kids, lvl, base, 0, n, lab, tgt, ext)}
    case x:
      x

# parse_auto_dup (uses > 1): the rewritten body under its dup chain
def tm.auto_dup(body: Tm, +lvl: U32, +base: U32, +tgt: U32, +ext: U32, +uses: U32, +lab: U32) -> Tm:
  +n = (uses - 1 : U32)
  tm.chain(U32.to_nat(n), (n - 1 : U32), lvl, base, lab, tgt, ext, tm.adup.body(body, lvl, base, n, lab, tgt, ext))

# Layout in the heap
# ==================

def tm.arity.ctr(z: Bool, +t: U32) -> U32:
  match z:
    case True{}:
      (t - 13 : U32)
    case False{}:
      0

# TERM_ARITY for the tags a book term can hold
def tm.arity(+t: U32) -> U32:
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
      tm.arity.ctr(U32.is_le(14, x) && U32.is_le(x, 29), x)

# the words t's fields and their subtrees take (t's own word excluded)
def tm.size(t: Tm) -> U32:
  match t:
    case Tl{tag, e, val}:
      0
    case Tb{+tag, e, kids}:
      (tm.arity(tag) + tm.size(kids) : U32)
    case Tn{}:
      0
    case Tc{h, r}:
      (tm.size(h) + tm.size(r) : U32)

# t's own word when its fields start at loc
def tm.word(t: Tm, +loc: U32) -> U32 & U32:
  match t:
    case Tl{+tag, +e, val}:
      (tm.hd(tag, e), val)
    case Tb{+tag, +e, kids}:
      (tm.hd(tag, e), loc)
    case x:
      (0, 0)

# One heap write: (loc, hi, lo)
type Wr is Data:
  Wr{loc: U32, hi: U32, lo: U32}

def tm.put(+loc: U32, w: U32 & U32, acc: List<&2, Wr>) -> List<&2, Wr>:
  (hi, lo) = w
  Wr{loc, hi, lo} <> acc

# the writes that lay t out: a node's fields go at a, their subtrees
# from a + arity on; in a field list, a is the next field's slot and b
# the next subtree's start
def tm.emit(t: Tm, +a: U32, +b: U32, acc: List<&2, Wr>) -> List<&2, Wr>:
  match t:
    case Tl{tag, e, val}:
      acc
    case Tb{+tag, e, kids}:
      tm.emit(kids, a, (a + tm.arity(tag) : U32), acc)
    case Tn{}:
      acc
    case Tc{+h, r}:
      tm.put(a, tm.word(h, b), tm.emit(h, b, 0, tm.emit(r, (a + 1 : U32), (b + tm.size(h) : U32), acc)))
