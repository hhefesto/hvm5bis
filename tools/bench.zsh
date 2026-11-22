#!/usr/bin/env zsh
# hvm5bis's benchmark shim: HVM4's devs/bench programs through upstream
# HVM4 and hvm5bis, one at a time, with -s (interactions, heap, time).
#
#   tools/bench.zsh HVM HVM5BIS HVM4_REPO OUTDIR
#
# fib_nat and u32_fib at their own size need ~1.8G heap words (~14 GB);
# they run here at a smaller size (fib 30n, u32_fib 34), named so. Both
# runtimes get the same files; outputs are compared byte for byte.
set -u
hvm=$1 me=$2 repo=$3 out=$4
mkdir -p $out
b=$repo/devs/bench
cp $b/cnot_24.hvm $b/gen_mul4k.hvm $b/lambda_eval.hvm $out/
sed 's/@main = @u32(@fib(34n),0)/@main = @u32(@fib(30n),0)/' $b/fib_nat.hvm > $out/fib_nat_30.hvm
sed 's/@main = @u32_fib(38)/@main = @u32_fib(34)/' $b/u32_fib.hvm > $out/u32_fib_34.hvm
for f in cnot_24 fib_nat_30 gen_mul4k lambda_eval u32_fib_34; do
  for who in hvm me; do
    bin=${(P)who}
    /usr/bin/env time -f "wall %e s, max rss %M KB" -o $out/$f.$who.time \
      env HVM5BIS_HEAP=31 timeout 900 $bin $out/$f.hvm -s > $out/$f.$who.out 2> $out/$f.$who.err
    tail -4 $out/$f.$who.out > $out/$f.$who.stats
    head -n -4 $out/$f.$who.out > $out/$f.$who.result
  done
  if cmp -s $out/$f.hvm.result $out/$f.me.result; then same=same; else same=DIFF; fi
  echo "== $f: output $same"
  for who in hvm me; do echo "  $who: $(tr '\n' ' ' < $out/$f.$who.stats) | $(cat $out/$f.$who.time)"; done
done
