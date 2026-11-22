# hvm5bis

A port of [HVM4](https://github.com/HigherOrderCO/HVM4), HigherOrderCO's
runtime for the Interaction Calculus, to [Bend 2](https://github.com/bendlang/bend).
It reads HVM4's input language and evaluates it as HVM4's `src/hvm.c` does:
the same terms, the same interaction rules, in the same order.

Work in progress: see "Status" below for what runs today.

## Layout

- `src/Tm.bend`: book (static) terms as a tree, HVM4's parse-time
  auto-dup pass, and their layout in the heap.
- `src/Wnf.bend`: the heap, the term words and the weak-normal-form
  machine with every interaction rule of HVM4's WNF section.
- `src/Parse.bend`: the parser (HVM4's Parse section).
- `tools/Order.hs`: puts a Bend file's defs in dependency order (Bend
  checks defs top to bottom and has no mutual recursion).

## Status

See the commit log; this section is filled in as parts pass HVM4's tests.

## Credits

- HVM4 is by Victor Taelin and the HigherOrderCO team. hvm5bis translates
  HVM4's `src/hvm.c` at commit `6defdfc` and runs HVM4's own tests and
  benchmarks; every rule and the syntax are HVM4's. HVM4 has no license
  file; see NOTICE.
- Bend is by Victor Taelin and HigherOrderCO (Apache-2.0); hvm5bis is
  written in Bend 2 and built with it.
