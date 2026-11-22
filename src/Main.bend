import Base
import ./Tm.bend as T
import ./Wnf.bend as W
import ./Parse.bend as Ps
import ./Print.bend as P
import ./Eval.bend as E

# hvm5bis: the command line, a port of the Runtime and CLI sections of
# HVM4's src/hvm.c.
#
#   hvm5bis FILE.hvm [-s] [-S] [-C[N]] [--collapse[=N]]
#
# It reads FILE (and its #includes), lays the book out in the heap,
# evaluates @main (normal form, or collapsed with -C) and prints what
# HVM4 prints. The heap holds 2^(HVM5BIS_HEAP - 1) words (HVM5BIS_HEAP
# defaults to 27).

# Options
# =======

def s.bytes(s: String) -> List<&2, U32>:
  P.tx(s)

def digits.of(cs: List<&2, U32>) -> U32:
  Ps.lx.dec(cs, 0)

def opt.lim(+cs: List<&2, U32>) -> U32:
  match cs:
    case Nil{}:
      4294967295
    case Con{h, t}:
      digits.of(Ps.lx.digits(cs))

def file.k3(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Maybe<&2, List<&2, U32>>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, List<&2, U32>>, None{})
    case Done{bs}:
      IO.pure(Maybe<&2, List<&2, U32>>, Some{bs})

def file.k2(fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Maybe<&2, List<&2, U32>>):
  (f, r) = fr
  do IO<Maybe<&2, List<&2, U32>>>:
    File.close(f)
    file.k3(r)

def file.k(r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, List<&2, U32>>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, List<&2, U32>>, None{})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>, Maybe<&2, List<&2, U32>>, File.read_bytes(f, 1073741824), file.k2)

# sys_file_read: the file's bytes, or none
def file.read(path: String) -> IO(Maybe<&2, List<&2, U32>>):
  IO.bind(Result<&1, &1, U32 & String, File>, Maybe<&2, List<&2, U32>>, File.open(path, "r"), file.k)

def path.dir.k(+rb: List<&2, U32>) -> List<&2, U32>:
  match rb:
    case Nil{}:
      Nil{}
    case Con{47, t}:
      List.reverse(&2, U32, rb)
    case Con{h, t}:
      path.dir.k(t)

# sys_path_join: rel against base's directory
def path.dir(+base: List<&2, U32>) -> List<&2, U32>:
  path.dir.k(List.reverse(&2, U32, base))

def path.join(+base: List<&2, U32>, +rel: List<&2, U32>) -> List<&2, U32>:
  match rel:
    case Con{47, t}:
      rel
    case x:
      List.append(&2, U32, path.dir(base), rel)

def bytes.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{+a, at} Con{+b, bt}:
      U32.is_eq(a, b) && bytes.eq(at, bt)
    case x y:
      False{}

def seen.has(ps: List<&2, List<&2, U32>>, +p: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{+x, t}:
      bytes.eq(x, p) || seen.has(t, p)

# Loading: parse_def over the file and its includes
# =================================================

# a suspended file: its path and the bytes left after the #include
type Fr is Data:
  Fr{path: List<&2, U32>, bytes: List<&2, U32>, rest: List<&2, U32>}

# where the loader is: parsing (r: the last parse of the file at path,
# whose bytes are bs), reading a file, done
type LS is Type:
  LStep{path: List<&2, U32>, bs: List<&2, U32>, seen: List<&2, List<&2, U32>>, r: Ps.PR<Ps.DR>, fs: List<&2, Fr>}
  LRead{full: List<&2, U32>, path: List<&2, U32>, bs: List<&2, U32>, seen: List<&2, List<&2, U32>>, r: Ps.PR<Ps.DR>, fs: List<&2, Fr>}
  LDone{r: Ps.PR<Ps.DR>, path: List<&2, U32>, bs: List<&2, U32>}

type LdR is Data:
  LOk{st: Ps.St}
  LErr{msg: String}

# (mode, path, seen, last parse, suspended files, file to read)
# mode 0: step on the parse, 1: read the pending file, 2: done
def defs(st: Ps.St) -> Ps.PR<Ps.DR>:
  Ps.P.defs(4294967295n, st)

def ld.resume(+p: List<&2, U32>, +b: List<&2, U32>, rest: List<&2, U32>, seen: List<&2, List<&2, U32>>, t: List<&2, Fr>, r: Ps.PR<Ps.DR>) -> LS:
  match r:
    case Ps.POk{st, d}:
      LStep{p, b, seen, defs(Ps.st.set_src(st, rest)), t}
    case Ps.PEr{e, at}:
      LDone{Ps.PEr{e, at}, p, b}

def ld.done(r: Ps.PR<Ps.DR>, +path: List<&2, U32>, +bs: List<&2, U32>, seen: List<&2, List<&2, U32>>, fs: List<&2, Fr>) -> LS:
  match fs:
    case Nil{}:
      LDone{r, path, bs}
    case Con{Fr{+p, +b, rest}, t}:
      ld.resume(p, b, rest, seen, t, r)

def ld.inc(z: Bool, +full: List<&2, U32>, +path: List<&2, U32>, +bs: List<&2, U32>, seen: List<&2, List<&2, U32>>, fs: List<&2, Fr>, +st: Ps.St) -> LS:
  match z:
    case True{}:
      LStep{path, bs, seen, defs(st), fs}
    case False{}:
      LRead{full, full, Nil{}, full <> seen, Ps.POk{st, Ps.DDone{}}, Fr{path, bs, Ps.st.src(st)} <> fs}

def ld.step(+path: List<&2, U32>, +bs: List<&2, U32>, +seen: List<&2, List<&2, U32>>, r: Ps.PR<Ps.DR>, fs: List<&2, Fr>) -> LS:
  match r:
    case Ps.PEr{e, at}:
      LDone{Ps.PEr{e, at}, path, bs}
    case Ps.POk{st, Ps.DDone{}}:
      ld.done(Ps.POk{st, Ps.DDone{}}, path, bs, seen, fs)
    case Ps.POk{st, Ps.DInc{+nm}}:
      ld.inc(seen.has(seen, path.join(path, nm)), path.join(path, nm), path, bs, seen, fs, st)

def ld.read(+full: List<&2, U32>, +path: List<&2, U32>, seen: List<&2, List<&2, U32>>, r: Ps.PR<Ps.DR>, fs: List<&2, Fr>, got: Maybe<&2, List<&2, U32>>) -> LS:
  match r got:
    case x None{}:
      LDone{Ps.PEr{"Error: could not open '" ++ Ps.lx.str(full) ++ "'", Nil{}}, path, Nil{}}
    case Ps.POk{st, d} Some{+bs}:
      LStep{path, bs, seen, defs(Ps.st.set_src(st, bs)), fs}
    case Ps.PEr{e, at} Some{bs}:
      LDone{Ps.PEr{e, at}, path, bs}

# (line, col) after the first n bytes, as parse_advance counts them
def put.all(ws: List<&2, T.Wr>, h: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      h
    case Con{T.Wr{+loc, +hi, +lo}, t}:
      put.all(t, W.wr(h, loc, hi, lo))

def has.def(ds: List<&2, Ps.Df>, +id: U32) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Ps.Df{+i, tm}, t}:
      U32.is_eq(i, id) || has.def(t, id)

# Running
# =======

def er.msg(+er: U32) -> String:
  match er:
    case 1:
      "RUNTIME_ERROR: cannot apply a number"
    case 2:
      "RUNTIME_ERROR: cannot apply a constructor"
    case 3:
      "Out of heap memory"
    case 4:
      "wnf: stack overflow"
    case x:
      "RUNTIME_ERROR: out of fuel"

def out.chars(cs: List<&2, U32>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Chr{c} <> out.chars(t)

def out.write(cs: List<&2, U32>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      IO.write(String.from_list(out.chars(Con{h, t})))

def fail.er(+er: U32) -> IO(Unit):
  match er:
    case 0:
      IO.pure(Unit, Unit{})
    case x:
      do IO<Unit>:
        IO.print_err(er.msg(x))
        IO.exit(1)

def run.norm.t(s: Array<U32>, +nx: U32, it: Nat, +fr: U32, +er: U32, +hl: U32, r: Array<U32> & List<&2, U32>) -> E.M() & List<&2, U32>:
  (h, txt) = r
  ((h, s, nx, it, fr, er, hl), List.append(&2, U32, txt, [10]))

def run.norm.q(z: Bool, +env: P.Env, m: E.M(), +hi: U32, +lo: U32) -> E.M() & List<&2, U32>:
  match z:
    case True{}:
      (m, Nil{})
    case False{}:
      (h, s, nx, it, fr, er, hl) = m
      run.norm.t(s, nx, it, fr, er, hl, P.print(env, 0, h, hi, lo))

def run.norm.p(+env: P.Env, +silent: Bool, r: E.R()) -> E.M() & List<&2, U32>:
  ((h, s, nx, it, fr, +er, hl), +hi, lo0) = r
  +lo = {lo0 : U32}
  run.norm.q(U32.is_ne(er, 0) || silent, env, (h, s, nx, it, fr, er, hl), hi, lo)

# eval_normalize, then print_term (unless silent)
def run.norm.k(+env: P.Env, +silent: Bool, +root: U32, r: E.M() & Array<U32>) -> E.M() & List<&2, U32>:
  (m, seen) = r
  run.norm.p(env, silent, E.m.rd(m, root))

def heap.depth.k(r: Maybe<&2, U32>) -> Nat:
  match r:
    case None{}:
      27n
    case Some{n}:
      U32.to_nat(n)

def heap.depth(r: Result<&1, &1, U32 & String, String>) -> Nat:
  match r:
    case Fail{e}:
      27n
    case Done{s}:
      heap.depth.k(U32.read(s))

def show.pad3.k(a: Bool, b: Bool, +n: Nat) -> String:
  match a b:
    case True{} _:
      "00" ++ Nat.show(n)
    case False{} True{}:
      "0" ++ Nat.show(n)
    case False{} False{}:
      Nat.show(n)

def show.pad3(+n: Nat) -> String:
  show.pad3.k(Nat.is_lt(n, 10n), Nat.is_lt(n, 100n), n)

def show.ms(+ms: Nat) -> String:
  Nat.show(Nat.div(ms, 1000n)) ++ "." ++ show.pad3(Nat.mod(ms, 1000n))

def show.pad2.k(a: Bool, +n: Nat) -> String:
  match a:
    case True{}:
      "0" ++ Nat.show(n)
    case False{}:
      Nat.show(n)

def show.pad2(+n: Nat) -> String:
  show.pad2.k(Nat.is_lt(n, 10n), n)
def show.perf.k(+c: Nat, z: Bool) -> String:
  match z:
    case True{}:
      "inf"
    case False{}:
      Nat.show(Nat.div(c, 100n)) ++ "." ++ show.pad2(Nat.mod(c, 100n))

# M interactions per second with two decimals, from a count and ms
def show.perf(+it: Nat, +ms: Nat) -> String:
  show.perf.k(Nat.div(Nat.mul(it, 100n), Nat.mul(Nat.add(ms, 0n), 1000n)), Nat.is_eq(ms, 0n))

def stats(z: Bool, +si: Bool, +it: Nat, +heap: U32, +ms: Nat) -> IO(Unit):
  match z si:
    case True{} _:
      IO.print("- Itrs: " ++ Nat.show(it) ++ " interactions\n- Heap: " ++ U32.show(heap) ++ " nodes\n- Time: " ++ show.ms(ms) ++ " seconds\n- Perf: " ++ show.perf(it, ms) ++ " M interactions/s")
    case False{} True{}:
      IO.print("- Itrs: " ++ Nat.show(it) ++ " interactions")
    case False{} False{}:
      IO.pure(Unit, Unit{})

type Opt is Data:
  Opt{file: String, collapse: Bool, limit: U32, stats: Bool, silent: Bool, bad: String}

def opt.set.file(o: Opt, a: String) -> Opt:
  match o:
    case Opt{f, c, l, st, si, b}:
      Opt{a, c, l, st, si, b}

# atoi on what follows -C (no digits: 0, as atoi answers)
def opt.collapse(o: Opt, cs: List<&2, U32>) -> Opt:
  match o:
    case Opt{f, c, l, st, si, b}:
      Opt{f, True{}, opt.lim(cs), st, si, b}

def opt.stats(o: Opt) -> Opt:
  match o:
    case Opt{f, c, l, st, si, b}:
      Opt{f, c, l, True{}, si, b}

def opt.silent(o: Opt) -> Opt:
  match o:
    case Opt{f, c, l, st, si, b}:
      Opt{f, c, l, st, True{}, b}

def opt.bad(o: Opt, a: String) -> Opt:
  match o:
    case Opt{f, c, l, st, si, b}:
      Opt{f, c, l, st, si, a}

def opt.long.k(c: Bool, s: Bool, si: Bool, +cs: List<&2, U32>, o: Opt, a: String) -> Opt:
  match c s si:
    case True{} _ _:
      opt.collapse(o, Ps.lx.drop(11n, cs))
    case False{} True{} _:
      opt.stats(o)
    case False{} False{} True{}:
      opt.silent(o)
    case False{} False{} False{}:
      opt.bad(o, a)

def opt.long(+cs: List<&2, U32>, o: Opt, a: String) -> Opt:
  opt.long.k(Ps.lx.starts(s.bytes("--collapse"), cs), Ps.lx.starts(s.bytes("--stats"), cs), Ps.lx.starts(s.bytes("--silent"), cs), cs, o, a)

def opt.one.k(+cs: List<&2, U32>, o: Opt, a: String) -> Opt:
  match cs:
    case Con{45, Con{67, rest}}:
      opt.collapse(o, rest)
    case Con{45, Con{115, Nil{}}}:
      opt.stats(o)
    case Con{45, Con{83, Nil{}}}:
      opt.silent(o)
    case Con{45, x}:
      opt.long(cs, o, a)
    case x:
      opt.set.file(o, a)

def opt.one(o: Opt, +a: String) -> Opt:
  opt.one.k(s.bytes(a), o, a)

def opts(xs: List<&1, String>, o: Opt) -> Opt:
  match xs:
    case Nil{}:
      o
    case Con{+a, t}:
      opts(t, opt.one(o, a))

# Files
# =====

def opt.stats.of(+o: Opt) -> Bool:
  match o:
    case Opt{f, c, l, st, si, b}:
      st

def opt.silent.of(+o: Opt) -> Bool:
  match o:
    case Opt{f, c, l, st, si, b}:
      si

# the result of a run: the machine and the text
def fin(+o: Opt, +t0: Nat, r: E.M() & List<&2, U32>) -> IO(Unit):
  ((h, s, +nx, +it, fr, +er, hl), txt) = r
  do IO<Unit>:
    out.write(txt)
    fail.er(er)
    t1 : Nat <- IO.now()
    stats(opt.stats.of(o), opt.silent.of(o), it, (nx - 1 : U32), Nat.sub(t1, t0))

def opt.collapse.of(+o: Opt) -> Bool:
  match o:
    case Opt{f, c, l, st, si, b}:
      c

def opt.limit.of(+o: Opt) -> U32:
  match o:
    case Opt{f, c, l, st, si, b}:
      l

def run.coll(+lim: U32, +o: Opt, +env: P.Env, m: E.M(), +root: U32) -> E.M() & List<&2, U32>:
  match lim:
    case 0:
      (m, Nil{})
    case x:
      E.collapse(env, E.Cfg{x, opt.stats.of(o), opt.silent.of(o)}, m, root)

def run.eval.k(c: Bool, +o: Opt, +env: P.Env, +mid: U32, r: E.M() & U32, seen: Array<U32>) -> E.M() & List<&2, U32>:
  match c:
    case True{}:
      (m, root0) = r
      +root = {root0 : U32}
      run.coll(opt.limit.of(o), o, env, E.m.wr(m, root, W.hd(8, mid), 0), root)
    case False{}:
      (m, root0) = r
      +root = {root0 : U32}
      run.norm.k(env, opt.silent.of(o), root, E.snf(E.m.wr(m, root, W.hd(8, mid), 0), seen, root))
def run.eval(+o: Opt, +env: P.Env, +mid: U32, m: E.M(), seen: Array<U32>) -> E.M() & List<&2, U32>:
  run.eval.k(opt.collapse.of(o), o, env, mid, E.m.alloc(m, 1), seen)

def run.lay(+o: Opt, +dep: Nat, +env: P.Env, +mid: U32, r: Array<U32> & U32) -> IO(Unit):
  (h, nx0) = r
  +nx = {nx0 : U32}
  do IO<Unit>:
    s : Array<U32> = Array.new(U32, 24n, 0)
    seen : Array<U32> = Array.new(U32, Nat.sub(dep, 6n), 0)
    t0 : Nat <- IO.now()
    fin(o, t0, run.eval(o, env, mid, (h, s, nx, 0n, 1, 0, (U32.shln(1, Nat.sub(dep, 1n)) - 64 : U32)), seen))

# realpath for a relative name: against $PWD (./ dropped)
def lay1.k(+id: U32, +nx: U32, h: Array<U32>, r: List<&2, T.Wr> & U32) -> Array<U32> & U32:
  (ws, nx20) = r
  +nx2 = {nx20 : U32}
  (W.wr(put.all(ws, h), (id + 1 : U32), 0, nx), nx2)

def lay1(+id: U32, +tm: T.Tm, st: Array<U32> & U32) -> Array<U32> & U32:
  (h, nx0) = st
  +nx = {nx0 : U32}
  lay1.k(id, nx, h, T.tm.place(tm, nx, (Nil{}, (nx + 1 : U32))))

# each definition at nx: its word, then its fields; BOOK[id] (word 1 + id)
# holds its location
def lay(ds: List<&2, Ps.Df>, st: Array<U32> & U32) -> Array<U32> & U32:
  match ds:
    case Nil{}:
      st
    case Con{Ps.Df{+id, +tm}, t}:
      lay(t, lay1(id, tm, st))
# the book laid out; @main evaluated
def run.book(+o: Opt, +dep: Nat, st: Ps.St, +mid: U32) -> IO(Unit):
  match st:
    case Ps.St{src, binds, flab, fside, tab, +names, +ntab, +book}:
      run.lay(o, dep, P.Env{names, ntab}, mid, lay(List.reverse(&2, Ps.Df, book), (Array.new(U32, dep, 0), (ntab + 1 : U32))))

def run.main.k(z: Bool, +o: Opt, +dep: Nat, st: Ps.St, +id: U32) -> IO(Unit):
  match z:
    case True{}:
      run.book(o, dep, st, id)
    case False{}:
      do IO<Unit>:
        IO.print_err("Error: @main not defined")
        IO.exit(1)

def run.main(+o: Opt, +dep: Nat, r: Ps.SI) -> IO(Unit):
  match r:
    case Ps.SI{+st, +id}:
      run.main.k(has.def(Ps.st.book(st), id), o, dep, st, id)

def run.loaded(+o: Opt, +dep: Nat, r: LdR) -> IO(Unit):
  match r:
    case LErr{e}:
      do IO<Unit>:
        IO.print_err(e)
        IO.exit(1)
    case LOk{st}:
      run.main(o, dep, Ps.tab.find("main", st))

# each definition at nx: its word, then its fields; BOOK[id] (word 1 + id)
# holds its location
def lc(k: Nat, bs: List<&2, U32>, +l: U32, +c: U32) -> U32 & U32:
  match k bs:
    case 0n x:
      (l, c)
    case x Nil{}:
      (l, c)
    case 1n+q Con{+b, t}:
      match b:
        case 10:
          lc(q, t, (l + 1 : U32), 1)
        case y:
          lc(q, t, l, (c + 1 : U32))

def loc.text(+path: List<&2, U32>, r: U32 & U32) -> List<&2, U32>:
  (+l, c0) = r
  +c = {c0 : U32}
  List.append(&2, U32, P.tx(" ("), List.append(&2, U32, path, P.tx(":" ++ U32.show(l) ++ ":" ++ U32.show(c) ++ ")")))

# the PARSE_ERROR header's location: (file:line:col) where the error was
def loc.fill(cs: List<&2, U32>, +loc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      match c:
        case 1:
          List.append(&2, U32, loc, loc.fill(t, loc))
        case x:
          x <> loc.fill(t, loc)

def ld.err(+e: String, +at: List<&2, U32>, +path: List<&2, U32>, +bs: List<&2, U32>) -> String:
  String.from_list(out.chars(loc.fill(P.tx(e), loc.text(path, lc(Nat.sub(List.length(&2, U32, bs), List.length(&2, U32, at)), bs, 1, 1)))))

def ld.fin(r: Ps.PR<Ps.DR>, +path: List<&2, U32>, +bs: List<&2, U32>) -> IO(LdR):
  match r:
    case Ps.POk{st, d}:
      IO.pure(LdR, LOk{st})
    case Ps.PEr{+e, +at}:
      IO.pure(LdR, LErr{ld.err(e, at, path, bs)})

def ld(k: Nat, s: LS) -> IO(LdR):
  match k:
    case 0n:
      IO.pure(LdR, LErr{"too many includes"})
    case 1n+q:
      match s:
        case LStep{+path, +bs, +seen, r, fs}:
          ld(q, ld.step(path, bs, seen, r, fs))
        case LRead{+full, +path, bs, +seen, r, fs}:
          IO.bind(Maybe<&2, List<&2, U32>>, LdR, file.read(Ps.lx.str(full)), got => ld(q, ld.read(full, path, seen, r, fs, got)))
        case LDone{r, +path, +bs}:
          ld.fin(r, path, bs)

def abs.path.k(pwd: Result<&1, &1, U32 & String, String>, +f: List<&2, U32>) -> List<&2, U32>:
  match pwd:
    case Fail{e}:
      f
    case Done{d}:
      List.append(&2, U32, P.tx(d), 47 <> f)

def abs.path(pwd: Result<&1, &1, U32 & String, String>, +f: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Con{47, t}:
      f
    case Con{46, Con{47, t}}:
      abs.path.k(pwd, t)
    case x:
      abs.path.k(pwd, x)

def run.src(+o: Opt, +dep: Nat, +path: List<&2, U32>, got: Maybe<&2, List<&2, U32>>) -> IO(Unit):
  match got:
    case None{}:
      do IO<Unit>:
        IO.print_err("Error: could not open '" ++ Ps.lx.str(path) ++ "'")
        IO.exit(1)
    case Some{+bs}:
      do IO<Unit>:
        pwd : Result<&1, &1, U32 & String, String> <- IO.get_env("PWD")
        +ap : List<&2, U32> = abs.path(pwd, path)
        r : LdR <- ld(65536n, LStep{ap, bs, [ap], defs(Ps.st.new(bs)), Nil{}})
        run.loaded(o, dep, r)
def run.k(ok: Bool, nofile: Bool, +o: Opt, +dep: Nat, +f: String, +b: String) -> IO(Unit):
  match ok nofile:
    case False{} _:
      do IO<Unit>:
        IO.print_err("Unknown option: " ++ b)
        IO.exit(1)
    case True{} True{}:
      IO.print("hvm5bis: a port of HVM4 to Bend\n\nUsage: hvm5bis <file.hvm> [-s] [-S] [-C[N]]")
    case True{} False{}:
      IO.bind(Maybe<&2, List<&2, U32>>, Unit, file.read(f), got => run.src(o, dep, s.bytes(f), got))

def run(+o: Opt, +dep: Nat) -> IO(Unit):
  match o:
    case Opt{+f, c, l, st, si, +b}:
      run.k(String.is_empty(b), String.is_empty(f), o, dep, f, b)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    hd : Result<&1, &1, U32 & String, String> <- IO.get_env("HVM5BIS_HEAP")
    run(opts(List.drop(&1, String, args, 1n), Opt{"", False{}, 4294967295, False{}, False{}, ""}), heap.depth(hd))

