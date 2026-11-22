import Base
import ./Tm.bend as T
import ./Wnf.bend as W

def put.all(ws: List<&2, T.Wr>, h: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      h
    case Con{T.Wr{+loc, +hi, +lo}, t}:
      put.all(t, W.wr(h, loc, hi, lo))

# @main = ((λa.λb.a) 1 2)
def prog() -> T.Tm:
  T.tm.app(T.tm.app(T.tm.lam(1, T.tm.lam(U32.or(2, 8388608), T.tm.bjv(1))), T.tm.num(1)), T.tm.num(2))

def fin(r: W.S() & U32 & U32) -> String:
  ((h, s, nx, it, fr, er, hl), +th, tl) = r
  "tag " ++ U32.show(W.tg(th)) ++ " val " ++ U32.show(tl) ++ " itrs " ++ Nat.show(it) ++ " er " ++ U32.show(er) ++ " nx " ++ U32.show(nx)

def main() -> IO(Unit):
  +t = prog()
  +r = {2 : U32}
  h = Array.new(U32, 20n, 0)
  h = W.wr(h, 1, 0, r)
  h = put.all(T.tm.put(r, T.tm.word(t, (r + 1 : U32)), T.tm.emit(t, (r + 1 : U32), 0, Nil{})), h)
  +nx = (r + 1 + T.tm.size(t) : U32)
  s = Array.new(U32, 24n, 0)
  IO.print(fin(W.wnf((h, s, nx, 0n, 1, 0, 524000), W.hd(8, 0), 0)))
