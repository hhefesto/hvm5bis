import Base

# hvm5bis's gate: HVM4's own test runner (devs/test/_all_.sh) in Bend.
#
#   gate HVM HVM5BIS TIMEOUT_MS TEST.hvm...
#
# For each test it reads the expected output from the file's trailing //
# lines and its CLI flags from its leading //! lines, exactly as _all_.sh
# does, runs both runtimes on it (stderr then stdout, as a C program's
# buffered stdout lands after its stderr, ANSI colors stripped, trailing
# newlines dropped) and checks each against the expectation. It prints a
# line per test and the totals: how many each runtime passes, and how
# many tests give both the same output.

def T() -> Data:
  List<&2, U32>

def tx.go(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Char.to_u32(c) <> tx.go(t)

def tx(s: String) -> T():
  tx.go(String.to_list(s))

def str.go(cs: T()) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Chr{c} <> str.go(t)

def str(cs: T()) -> String:
  String.from_list(str.go(cs))

def starts(p: T(), +s: T()) -> Bool:
  match p s:
    case Nil{} x:
      True{}
    case Con{+a, pt} Con{+b, st}:
      U32.is_eq(a, b) && starts(pt, st)
    case x y:
      False{}

def drop(k: Nat, +s: T()) -> T():
  match k s:
    case 0n x:
      x
    case x Nil{}:
      Nil{}
    case 1n+q Con{h, t}:
      drop(q, t)

def eq(a: T(), b: T()) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{+x, at} Con{+y, bt}:
      U32.is_eq(x, y) && eq(at, bt)
    case x y:
      False{}

def contains(k: Nat, +p: T(), +s: T()) -> Bool:
  match k s:
    case 0n x:
      False{}
    case x Nil{}:
      eq(p, Nil{})
    case 1n+q Con{h, t}:
      starts(p, s) || contains(q, p, t)

# words split on spaces
def lines.end(cur: T(), acc: List<&2, T()>) -> List<&2, T()>:
  match cur:
    case Nil{}:
      List.reverse(&2, T(), acc)
    case Con{h, t}:
      List.reverse(&2, T(), List.reverse(&2, U32, Con{h, t}) <> acc)

# lines of a text (a final newline ends the last line)
def lines.go(cs: T(), cur: T(), acc: List<&2, T()>) -> List<&2, T()>:
  match cs:
    case Nil{}:
      lines.end(cur, acc)
    case Con{+c, t}:
      match c:
        case 10:
          lines.go(t, Nil{}, List.reverse(&2, U32, cur) <> acc)
        case x:
          lines.go(t, x <> cur, acc)

def lines(cs: T()) -> List<&2, T()>:
  lines.go(cs, Nil{}, Nil{})

def join.k(t: List<&2, T()>, x: T()) -> T():
  match t:
    case Nil{}:
      x
    case Con{y, u}:
      List.append(&2, U32, x, 10 <> join.k(u, y))

def join(xs: List<&2, T()>) -> T():
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      join.k(t, x)
def words.push(cur: T(), acc: List<&2, T()>) -> List<&2, T()>:
  match cur:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse(&2, U32, Con{h, t}) <> acc

# words split on spaces
def words.go(cs: T(), cur: T(), acc: List<&2, T()>) -> List<&2, T()>:
  match cs:
    case Nil{}:
      List.reverse(&2, T(), words.push(cur, acc))
    case Con{+c, t}:
      match c:
        case 32:
          words.go(t, Nil{}, words.push(cur, acc))
        case x:
          words.go(t, x <> cur, acc)

def words(cs: T()) -> List<&2, T()>:
  words.go(cs, Nil{}, Nil{})

def lines.blank(+l: T()) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

type Ex is Data:
  Ex{lines: List<&2, T()>, n: U32, prefix: T(), contains: T(), nocol: Bool}

# strip ANSI color codes ESC [ digits/; m (mode 0 text, 1 after ESC, 2 in a code)
def ex.line(p: Bool, c: Bool, n: Bool, +l: T(), e: Ex) -> Ex:
  match p c n:
    case True{} _ _:
      match e:
        case Ex{ls, +k, pf, ct, +nc}:
          Ex{ls, k, drop(16n, l), ct, nc}
    case False{} True{} _:
      match e:
        case Ex{ls, +k, pf, ct, +nc}:
          Ex{ls, k, pf, drop(18n, l), nc}
    case False{} False{} True{}:
      match e:
        case Ex{ls, +k, pf, ct, +nc}:
          Ex{drop(3n, l) <> ls, (k + 1 : U32), pf, ct, True{}}
    case False{} False{} False{}:
      match e:
        case Ex{ls, +k, pf, ct, +nc}:
          Ex{drop(2n, l) <> ls, (k + 1 : U32), pf, ct, nc}

def trim.nl.r(cs: T()) -> T():
  match cs:
    case Con{10, t}:
      trim.nl.r(t)
    case x:
      x

def trim.nl(cs: T()) -> T():
  List.reverse(&2, U32, trim.nl.r(List.reverse(&2, U32, cs)))

def basename.k(rp: T(), acc: T()) -> T():
  match rp:
    case Nil{}:
      acc
    case Con{47, t}:
      acc
    case Con{+c, t}:
      basename.k(t, c <> acc)

def basename(+p: T()) -> T():
  basename.k(List.reverse(&2, U32, p), Nil{})

def strip.hvm(+n: T()) -> T():
  List.reverse(&2, U32, drop(4n, List.reverse(&2, U32, n)))

def check.k(nopf: Bool, noct: Bool, pe: Bool, +pf: T(), +ct: T(), +want: T(), +actual: T()) -> Bool:
  match nopf noct pe:
    case False{} _ _:
      starts(pf, actual)
    case True{} False{} _:
      contains(4294967295n, ct, actual)
    case True{} True{} True{}:
      starts(tx("PARSE_ERROR"), actual)
    case True{} True{} False{}:
      eq(want, actual)

# the verdict on one output
def check(+e: Ex, +actual: T()) -> Bool:
  match e:
    case Ex{+ls, n, +pf, +ct, nc}:
      check.k(lines.blank(pf), lines.blank(ct), eq(join(ls), tx("PARSE_ERROR")), pf, ct, join(ls), actual)

def strs(xs: List<&2, T()>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      str(x) <> strs(t)

def run.flags.k(nc: Bool, cnt: Bool, +n: U32, +top: List<&2, T()>) -> List<&2, String>:
  match nc cnt:
    case True{} _:
      strs(top)
    case False{} True{}:
      ("-C" ++ U32.show(n)) <> strs(top)
    case False{} False{}:
      "-C" <> strs(top)

# the flags _all_.sh passes
def run.flags(+name: T(), +e: Ex, +top: List<&2, T()>) -> List<&2, String>:
  match e:
    case Ex{ls, +n, pf, ct, +nc}:
      run.flags.k(nc, starts(tx("collapse_"), name) || starts(tx("enum_"), name), n, top)

# one runtime on one test: its cleaned output, or a timeout / failure
type Out is Data:
  OK{text: T()}
  NO{why: String}

def verdict(+e: Ex, +o: Out) -> Bool:
  match o:
    case OK{+t}:
      check(e, t)
    case NO{w}:
      False{}

def same(+a: Out, +b: Out) -> Bool:
  match a b:
    case OK{x} OK{y}:
      eq(x, y)
    case x y:
      False{}

def mark(b: Bool) -> String:
  match b:
    case True{}:
      "PASS"
    case False{}:
      "FAIL"

def show.out(+o: Out) -> String:
  match o:
    case OK{t}:
      str(t)
    case NO{w}:
      "<" ++ w ++ ">"

def detail(z: Bool, +o: Out) -> String:
  match z:
    case True{}:
      ""
    case False{}:
      "\n    hvm5bis: " ++ show.out(o)

# totals: tests, upstream passes, hvm5bis passes, same outputs
type Tot is Data:
  Tot{n: U32, up: U32, me: U32, sm: U32}

def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def tot.add(t: Tot, +a: Bool, +b: Bool, +c: Bool) -> Tot:
  match t:
    case Tot{n, up, me, sm}:
      Tot{(n + 1 : U32), (up + b2u(a) : U32), (me + b2u(b) : U32), (sm + b2u(c) : U32)}

def show.same(b: Bool) -> String:
  match b:
    case True{}:
      "same"
    case False{}:
      "DIFF"

def read.k3(r: Result<&1, &1, U32 & String, String>) -> IO(T()):
  match r:
    case Fail{e}:
      IO.pure(T(), Nil{})
    case Done{s}:
      IO.pure(T(), tx(s))

def read.k2(fr: File & Result<&1, &1, U32 & String, String>) -> IO(T()):
  (f, r) = fr
  do IO<T()>:
    File.close(f)
    read.k3(r)

def read.k(r: Result<&1, &1, U32 & String, File>) -> IO(T()):
  match r:
    case Fail{e}:
      IO.pure(T(), Nil{})
    case Done{f}:
      IO.bind(File & Result<&1, &1, U32 & String, String>, T(), File.read(f, 67108864), read.k2)

def read(path: String) -> IO(T()):
  IO.bind(Result<&1, &1, U32 & String, File>, T(), File.open(path, "r"), read.k)

def summary(t: Tot) -> IO(Unit):
  match t:
    case Tot{+n, up, me, sm}:
      IO.print("upstream HVM4: " ++ U32.show(up) ++ "/" ++ U32.show(n) ++ " pass\nhvm5bis:       " ++ U32.show(me) ++ "/" ++ U32.show(n) ++ " pass\nsame output:   " ++ U32.show(sm) ++ "/" ++ U32.show(n))

def ms.of.k(r: Maybe<&2, U32>) -> U32:
  match r:
    case None{}:
      60000
    case Some{n}:
      n

def ms.of(+s: String) -> U32:
  ms.of.k(U32.read(s))

type Ln is Data:
  Ln{flag: Bool, flagm: Bool, blank: Bool, com: Bool, pre: Bool, con: Bool, bang: Bool, l: T()}

# the leading directive lines: //! flags or //!-flags; blank lines skipped
def flags.top(ls: List<&2, Ln>) -> List<&2, T()>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Ln{True{}, b, c, d, e, f, g, +l}, t}:
      List.append(&2, T(), words(drop(4n, l)), flags.top(t))
    case Con{Ln{False{}, True{}, c, d, e, f, g, +l}, t}:
      List.append(&2, T(), words(drop(3n, l)), flags.top(t))
    case Con{Ln{False{}, False{}, True{}, d, e, f, g, l}, t}:
      flags.top(t)
    case Con{Ln{False{}, False{}, False{}, d, e, f, g, l}, t}:
      Nil{}

def ex.tail(rl: List<&2, Ln>, e: Ex) -> Ex:
  match rl:
    case Nil{}:
      e
    case Con{Ln{a, b, c, True{}, +p, +n, +g, +l}, t}:
      ex.tail(t, ex.line(p, n, g, l, e))
    case Con{Ln{a, b, c, False{}, p, n, g, l}, t}:
      e

def ln(+l: T()) -> Ln:
  Ln{starts(tx("//! "), l), starts(tx("//!-"), l), lines.blank(l), starts(tx("//"), l), starts(tx("//EXPECT_PREFIX:"), l), starts(tx("//EXPECT_CONTAINS:"), l), starts(tx("//!"), l), l}

def lns(ls: List<&2, T()>) -> List<&2, Ln>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      ln(l) <> lns(t)

# the leading directive lines: //! flags or //!-flags; blank lines skipped
def ansi.end(+mode: U32) -> T():
  match mode:
    case 1:
      [27]
    case x:
      Nil{}

def ansi.isd(+x: U32) -> Bool:
  U32.is_eq(x, 59) || (U32.is_le(48, x) && U32.is_le(x, 57))

def ansi.m2.k(z: Bool) -> U32:
  match z:
    case True{}:
      2
    case False{}:
      0

def ansi.e2.k(z: Bool, +x: U32) -> T():
  match z:
    case True{}:
      Nil{}
    case False{}:
      [x]
# the trailing // lines (rl: the lines from the end)
def ansi(cs: T(), +mode: U32) -> T():
  match cs:
    case Nil{}:
      ansi.end(mode)
    case Con{+c, t}:
      match c:
        case 27:
          match mode:
            case 0:
              ansi(t, 1)
            case 1:
              27 <> ansi(t, 1)
            case m:
              27 <> ansi(t, 0)
        case 91:
          match mode:
            case 1:
              ansi(t, 2)
            case m:
              91 <> ansi(t, 0)
        case 109:
          match mode:
            case 0:
              109 <> ansi(t, 0)
            case 1:
              27 <> (109 <> ansi(t, 0))
            case m:
              ansi(t, 0)
        case x:
          match mode:
            case 0:
              x <> ansi(t, 0)
            case 1:
              27 <> (x <> ansi(t, 0))
            case m:
              List.append(&2, U32, ansi.e2.k(ansi.isd(x), x), ansi(t, ansi.m2.k(ansi.isd(x))))

def out.k(v: U32 & (String & String)) -> Out:
  (code, oe) = v
  (o, e) = oe
  OK{trim.nl(ansi(List.append(&2, U32, tx(e), tx(o)), 0))}
def out.of(r: Result<&1, &1, U32 & String, U32 & (String & String)>) -> Out:
  match r:
    case Fail{e}:
      NO{"timeout or failure"}
    case Done{v}:
      out.k(v)

def dn(xs: List<&2, String>) -> List<&1, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x <> dn(t)
def run1(+bin: String, +file: String, +flags: List<&2, String>, +ms: U32) -> IO(Out):
  IO.bind(Result<&1, &1, U32 & String, U32 & (String & String)>, Out, Process.run(bin, dn(file <> flags), "", 67108864, ms), r => IO.pure(Out, out.of(r)))

def test.k(+name: T(), +e: Ex, +top: List<&2, T()>, +up: String, +me: String, +ms: U32, +file: String, tot: Tot) -> IO(Tot):
  do IO<Tot>:
    +a : Out <- run1(up, file, run.flags(name, e, top), 2000)
    +b : Out <- run1(me, file, run.flags(name, e, top), ms)
    IO.print("[" ++ mark(verdict(e, a)) ++ " " ++ mark(verdict(e, b)) ++ " " ++ show.same(same(a, b)) ++ "] " ++ str(name) ++ detail(verdict(e, b), b))
    return tot.add(tot, verdict(e, a), verdict(e, b), same(a, b))

def test.src(+file: String, +up: String, +me: String, +ms: U32, tot: Tot, +src: T()) -> IO(Tot):
  test.k(strip.hvm(basename(tx(file))), ex.tail(List.reverse(&2, Ln, lns(lines(src))), Ex{Nil{}, 0, Nil{}, Nil{}, False{}}), flags.top(lns(lines(src))), up, me, ms, file, tot)

def tests(fs: List<&1, String>, +up: String, +me: String, +ms: U32, tot: Tot) -> IO(Tot):
  match fs:
    case Nil{}:
      IO.pure(Tot, tot)
    case Con{+f, t}:
      do IO<Tot>:
        +src : T() <- read(f)
        tot2 : Tot <- test.src(f, up, me, ms, tot, src)
        tests(t, up, me, ms, tot2)

def go(args: List<&1, String>) -> IO(Unit):
  match args:
    case Con{prog, Con{+up, Con{+me, Con{+ms, fs}}}}:
      IO.bind(Tot, Unit, tests(fs, up, me, ms.of(ms), Tot{0, 0, 0, 0}), summary)
    case x:
      IO.print("usage: gate HVM HVM5BIS TIMEOUT_MS TEST.hvm...")

def main() -> IO(Unit):
  IO.bind(List<String>, Unit, IO.args(), go)
