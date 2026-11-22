import Base
import ./LAWS.bend as L

# hvm5bis's proofs of LAWS.bend: each law holds by computation ({==}):
# the OP2 laws for all operands, by op2's match on its code (and, for
# division by zero, on the operand's word).

def L.op.add(a, b):
  {==}

def L.op.sub(a, b):
  {==}

def L.op.mul(a, b):
  {==}

def L.op.div(a, b):
  {==}

def L.op.mod.zero(a):
  {==}

def L.op.and(a, b):
  {==}

def L.op.or(a, b):
  {==}

def L.op.xor(a, b):
  {==}

def L.op.lsh(a, b):
  {==}

def L.op.rsh(a, b):
  {==}

def L.op.not(a, b):
  {==}

def L.op.eq(a, b):
  {==}

def L.op.ne(a, b):
  {==}

def L.op.lt(a, b):
  {==}

def L.op.le(a, b):
  {==}

def L.op.gt(a, b):
  {==}

def L.op.ge(a, b):
  {==}

def L.op.other(a, b):
  {==}

def L.word.tag.lam():
  {==}

def L.word.ext.sup():
  {==}

def L.word.sub.tag():
  {==}

def L.alpha.a():
  {==}

def L.alpha.z():
  {==}

def L.alpha.aa():
  {==}

def L.alpha.none():
  {==}

def L.nick.roundtrip.L():
  {==}

def L.nick.roundtrip.abc():
  {==}

def L.key.credit():
  {==}

def L.key.floor():
  {==}

def L.op.div.zero(a):
  match a:
    case U32{aw}:
      {==}
