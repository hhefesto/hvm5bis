import Base
import ./src/Wnf.bend as W
import ./src/Print.bend as P
import ./src/Parse.bend as Ps
import ./src/Eval.bend as E

# hvm5bis's laws: what parts of the port mean, stated against HVM4's C.
# PROOF.bend proves each; `bend PROOF.bend --verdict` rechecks the proofs
# with BendTT's kernel.

# OP2 (term_op2_u32): each op code computes what hvm.c's switch does, for
# every pair of operands. Shifts mask their count to 5 bits (what x86's
# shl/shr do with hvm.c's `a << b`); ~ ignores its left operand; division
# and remainder by zero answer 0; codes past 16 answer 0.

law op.add:
  for a: U32
  for b: U32
  {W.op2(0, a, b) == (a + b : U32) : U32}

law op.sub:
  for a: U32
  for b: U32
  {W.op2(1, a, b) == (a - b : U32) : U32}

law op.mul:
  for a: U32
  for b: U32
  {W.op2(2, a, b) == (a * b : U32) : U32}

law op.div:
  for a: U32
  for b: U32
  {W.op2(3, a, b) == U32.div(a, b) : U32}

law op.div.zero:
  for a: U32
  {W.op2(3, a, 0) == 0 : U32}

law op.mod.zero:
  for a: U32
  {W.op2(4, a, 0) == 0 : U32}

law op.and:
  for a: U32
  for b: U32
  {W.op2(5, a, b) == U32.and(a, b) : U32}

law op.or:
  for a: U32
  for b: U32
  {W.op2(6, a, b) == U32.or(a, b) : U32}

law op.xor:
  for a: U32
  for b: U32
  {W.op2(7, a, b) == U32.xor(a, b) : U32}

law op.lsh:
  for a: U32
  for b: U32
  {W.op2(8, a, b) == U32.shln(a, U32.to_nat(U32.and(b, 31))) : U32}

law op.rsh:
  for a: U32
  for b: U32
  {W.op2(9, a, b) == U32.shrn(a, U32.to_nat(U32.and(b, 31))) : U32}

law op.not:
  for a: U32
  for b: U32
  {W.op2(10, a, b) == U32.not(b) : U32}

law op.eq:
  for a: U32
  for b: U32
  {W.op2(11, a, b) == W.b2u(U32.is_eq(a, b)) : U32}

law op.ne:
  for a: U32
  for b: U32
  {W.op2(12, a, b) == W.b2u(U32.is_ne(a, b)) : U32}

law op.lt:
  for a: U32
  for b: U32
  {W.op2(13, a, b) == W.b2u(U32.is_lt(a, b)) : U32}

law op.le:
  for a: U32
  for b: U32
  {W.op2(14, a, b) == W.b2u(U32.is_le(a, b)) : U32}

law op.gt:
  for a: U32
  for b: U32
  {W.op2(15, a, b) == W.b2u(U32.is_gt(a, b)) : U32}

law op.ge:
  for a: U32
  for b: U32
  {W.op2(16, a, b) == W.b2u(U32.is_ge(a, b)) : U32}

law op.other:
  for a: U32
  for b: U32
  {W.op2(17, a, b) == 0 : U32}

# Term words: a word's tag and ext read back what hd packs (tags < 128,
# exts < 2^24), and the SUB bit leaves the tag alone.

law word.tag.lam:
  {W.tg(W.hd(2, 5)) == 2 : U32}

law word.ext.sup:
  {W.ex(W.hd(5, 16777215)) == 16777215 : U32}

law word.sub.tag:
  {W.tg(W.sub.on(W.hd(44, 7))) == 44 : U32}

# Names: print_alpha_name's bijective base 26 (1 a, 26 z, 27 aa, 0 _), and
# print_name / the parser's nick letters agree (a 24-bit label prints as
# the name the parser read).

law alpha.a:
  {P.alpha(1, 97) == [97] : List<&2, U32>}

law alpha.z:
  {P.alpha(26, 97) == [122] : List<&2, U32>}

law alpha.aa:
  {P.alpha(27, 97) == [97, 97] : List<&2, U32>}

law alpha.none:
  {P.alpha(0, 65) == [95] : List<&2, U32>}

law nick.roundtrip.L:
  {P.pname(Ps.lx.nick(Ps.lx.name([76]), 0)) == [76] : List<&2, U32>}

law nick.roundtrip.abc:
  {P.pname(Ps.lx.nick(Ps.lx.name([97, 98, 99]), 0)) == [97, 98, 99] : List<&2, U32>}

# The collapse order key: SUP depth less a sixteenth of the INC credit,
# floored at 0 (eval_collapse_order_key).

law key.credit:
  {E.ord.key(5, 32) == 3 : U32}

law key.floor:
  {E.ord.key(1, 100) == 0 : U32}
