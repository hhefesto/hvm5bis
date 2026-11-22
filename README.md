# hvm5bis

A port of [HVM4](https://github.com/HigherOrderCO/HVM4), HigherOrderCO's
runtime for the Interaction Calculus, to [Bend 2](https://github.com/bendlang/bend).
It reads HVM4's input language and evaluates it as HVM4's `src/hvm.c`
(commit `6defdfc`) does: the same parser and desugarings, the same heap
words, the same interaction rules applied in the same order (the
interaction counts match HVM4's on every program tried), the same printer
and the same collapser.

```
nix build                       # result/bin/hvm5bis
result/bin/hvm5bis FILE.hvm     # normal form of @main
result/bin/hvm5bis FILE.hvm -C  # collapsed: one line per branch (-C10: ten)
result/bin/hvm5bis FILE.hvm -s  # and interactions, heap words, time
nix flake check                 # every module type-checks; HVM4's tests (the gate)
```

`HVM5BIS_HEAP=N` sets the heap to 2^(N-1) words (default 27: 64M words,
512 MB); `HVM5BIS_STACK=N` the WNF stack to 2^(N-1) frames (default
HEAP - 3).

## Status

- Gate: HVM4's own tests (`devs/test`, 217 programs, run by
  `tools/Gate.bend` with the rules of HVM4's `devs/test/_all_.sh`): upstream
  HVM4 passes 215/217, hvm5bis passes the same 215/217, and gives
  byte-for-byte the same output (PARSE_ERROR messages and their
  `file:line:col` included) on all 215. The two failures are the same on
  both: `fib_small` needs more than `_all_.sh`'s 2 s on upstream (hvm5bis
  computes it, 5702887, with `HVM5BIS_HEAP=30`), and `spin` never ends.
- Benchmarks (`devs/bench`, `tools/bench.zsh`): same output and the same
  interaction count as upstream on all five; hvm5bis takes 1.4x to 4.0x
  upstream's time (1.9x to 4.8x its wall time, table below). `fib_nat` and
  `u32_fib` run at smaller sizes (`fib(30n)`, `u32_fib(34)`), as their own
  sizes need about 14 GB of heap.
- Not ported: `-D` (step-by-step trace) and `-d` (debug); the heap is a
  fixed-size Bend array (HVM4 maps 2^32 words lazily), so very large
  programs need `HVM5BIS_HEAP`; heap locations are 31-bit.
- Proofs: the modules type-check (`bend FILE --check-only` prints ALL
  PROOFS CHECK, which is a type check). No laws are stated or proved with
  `--verdict` yet.

## Meaning

A term is a word: tag, ext (label, name, op), val (heap location or
number). Variables are affine and linked: a VAR points to its lambda's
body slot, DP0/DP1 to their dup node's slot; when a binder interacts, its
slot is overwritten by the substituted term with the SUB bit set. Book
terms are static, with de Bruijn levels (BJV/BJ0/BJ1), and are expanded
one layer at a time by ALO (allocation) under a bind list.

The interaction rules (`src/Wnf.bend`, as in `hvm.c`'s WNF section):

| rule | before | after |
| --- | --- | --- |
| APP-LAM | `(λx.f a)` | `x ← a; f` |
| APP-SUP | `(&L{f,g} a)` | `! A &L = a; &L{(f A₀),(g A₁)}` |
| APP-ERA / -NAM / -DRY / -INC | `(&{} a)` / `(^n a)` / `(^(f x) a)` / `(↑f a)` | `&{}` / `^(^n a)` / `^(^(f x) a)` / `↑(f a)` |
| APP-MAT-CTR | `(λ{#K:h; m} #K{a,b})` / `(λ{#K:h; m} #L{..})` | `(h a b)` / `(m #L{..})` |
| APP-MAT-NUM | `(λ{n:h; m} #n)` / `(λ{n:h; m} #k)` | `h` / `(m #k)` |
| APP-MAT-SUP / MAT-INC | `(λ{..} &L{a,b})` / `(λ{..} ↑x)` | `! M &L = λ{..}; &L{(M₀ a),(M₁ b)}` / `↑(λ{..} x)` |
| DUP-LAM | `! F &L = λx.f` | `F₀ ← λx0.G₀; F₁ ← λx1.G₁; x ← &L{x0,x1}; ! G &L = f` |
| DUP-SUP | `! X &L = &R{a,b}` | L = R: `X₀ ← a; X₁ ← b`; else `X₀ ← &R{A₀,B₀}; X₁ ← &R{A₁,B₁}` with `! A &L = a; ! B &L = b` |
| DUP-NOD / -NAM | `! X &L = T{a,b,..}` | `X₀ ← T{A₀,B₀,..}; X₁ ← T{A₁,B₁,..}`, each field duplicated |
| ALO-VAR / -LAM / -DUP / -NOD | `@{s} n` / `@{s} λx.f` / `@{s} !x&L=v;t` / `@{s} T{..}` | `s[n]` / `λx'.@{x',s} f` / `! x' &L = @{s} v; @{x',s} t` / `T{@{s}..}` |
| OP2-NUM-NUM / -SUP / -INC / -ERA | `(#a op #b)` / `(&L{a,b} op y)` / `(↑x op y)` / `(&{} op y)` | `#(a op b)` / `&L{(a op Y₀),(b op Y₁)}` / `↑(x op y)` / `&{}` |
| DSU / DDU (NUM, SUP, INC, ERA) | `&(#n){a,b}` / `! X &(#n) = v; b` | `&n{a,b}` / `! X &n = v; b(X₀,X₁)`, and as OP2 on SUP/INC/ERA labels |
| USE-VAL / -SUP / -INC / -ERA | `(λ{f} x)` | `(f x)`, distributed over SUP, under INC, erased by ERA |
| EQL (NUM, LAM, CTR, MAT, USE, NAM, DRY, SUP, INC, ANY, ERA) | `(a === b)` | structural equality: numbers compared, lambdas under a fresh shared name, constructors field by field (each next field under an INC), SUP distributed, `*` equal to anything |
| AND / OR | `(#n .&. b)` / `(#n .\|. b)` | short-circuit on the left number; distributed over SUP |
| UNS | `! ${f,v}; t` | `t(λy.λ$x.y, $x)` |

WNF (`wnf`) walks the head with an explicit stack, as `hvm.c` does; SNF
(`src/Eval.bend`, `eval_normalize`) reduces every reachable location once;
the collapser (`cnf`, `eval_collapse`) lifts the first SUP of a term to the
top and enumerates branches in HVM4's priority order (SUP depth less INC
credit, then age).

## Layout

- `src/Tm.bend`: book terms as a tree, HVM4's parse-time auto-dup pass,
  and their layout in the heap.
- `src/Wnf.bend`: the heap, the term words and the WNF machine with every
  interaction rule.
- `src/Parse.bend`: the parser (HVM4's Parse section): one def over a
  selector, as Bend has no mutual recursion.
- `src/Print.bend`: the printer (dynamic and quoted terms).
- `src/Eval.bend`: SNF, CNF and the collapse queue.
- `src/Main.bend`: files, `#include`, the CLI.
- `tools/Gate.bend`: the gate; `tools/bench.zsh`: the benchmark shim;
  `tools/Order.hs`: puts a Bend file's defs in dependency order.

HVM4's tests and benchmarks are not copied here: the flake fetches HVM4
at `6defdfc` as an input.

## Credits

- HVM4 is by Victor Taelin and the HigherOrderCO team. hvm5bis translates
  HVM4's `src/hvm.c` at commit `6defdfc` and runs HVM4's own tests and
  benchmarks; every rule, the syntax and the tests are HVM4's. HVM4 has no
  license file; see NOTICE.
- Bend is by Victor Taelin and HigherOrderCO (Apache-2.0); hvm5bis is
  written in Bend 2 and built with it. An earlier session's draft of the
  WNF machine and the parser's lexer is the base of `src/Wnf.bend` and
  `src/Parse.bend`.
