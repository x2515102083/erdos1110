# The Exceptional Erdős-Lewin Coprime Nonrepresentables

This note gives the human-readable proof formalized in this repository.  It
proves the three exceptional pairwise-coprime nonrepresentable cases

```text
(p,q) = (5,2), (9,2), (5,3).
```

The theorem proved here is the pairwise-coprime strengthening of ordinary
infinitude.  Erdős and Lewin had already shown that, for two bases, ordinary
d-completeness occurs exactly for the unordered pair `{2,3}`.  They then asked
two further questions for the remaining pairs: one about density, and one about
whether there are infinitely many coprime nonrepresentables.  The present note
addresses only the latter question, and only for the three exceptional pairs
not covered by the Yu-Chen range theorem.

## Representations

Fix coprime integers `p > q >= 2`.  A positive integer `n` is
`(p,q)`-representable if

```text
n = sum_{(i,j) in A} p^i q^j
```

for some finite set `A` of pairs `(i,j)` of nonnegative integers, with the
condition that no selected summand divides another selected summand.

Because `gcd(p,q)=1`,

```text
p^i q^j divides p^i' q^j'    iff    i <= i' and j <= j'.
```

Thus a valid representation is exactly a finite antichain in `N^2` under the
coordinatewise order.  In particular, there is at most one selected point with
any fixed first coordinate, and at most one selected point with any fixed
second coordinate.

We prove the existence of a sequence `f : N -> N` such that every `f(n)` is
greater than `1`, `(p,q)`-nonrepresentable, coprime to `p*q`, and distinct
terms `f(m), f(n)` are pairwise coprime.

## Low-row synchronization

The main local lemma is a synchronization statement.

**Lemma 1.**  Let `a,M >= 1` and suppose

```text
p^a < q^M.
```

Let `A` be an antichain contained in the rectangle

```text
{0,...,a} x {0,...,M-1}.
```

If

```text
sum_{(i,j) in A} p^i q^j == p^a  (mod q^M),
```

then

```text
A = {(a,0)}.
```

**Proof.**  Put

```text
S = sum_{(i,j) in A} p^i q^j.
```

The congruence says that `q^M` divides `S - p^a`.  Since `p` and `q` are
coprime, `p^a` is not divisible by `q`; therefore `S` is not divisible by `q`.
Hence some selected point has second coordinate `0`.  By the antichain
condition, this point is unique.  Write it as `(t,0)`.

There are two cases.

First suppose `t = a`.  If there were any other selected point, choose one
with minimal positive second coordinate, say `(i,j)` with `0 < j < M`.  Then
`S - p^a` is divisible by `q^j`, but not by `q^(j+1)`: the unique term at
second coordinate `j` contributes `p^i q^j`, whose coefficient is nonzero
modulo `q`, while all later terms have larger second coordinate.  This
contradicts divisibility by `q^M`.  Hence no other point exists, and
`A={(a,0)}`.

Now suppose `t < a`.  Since `(t,0)` is selected, no point with first coordinate
`a` can be selected: such a point would be comparable with `(t,0)`.
We descend through the first coordinates from `a` to `0` and maintain the
following invariant.  For each `r`, define

```text
S_r = sum_{(i,j) in A, i >= r} p^i q^j.
```

We prove that

```text
p^a - S_r = p^r X_r
```

for some positive integer `X_r`.  For `r=a`, this holds with `X_a=1`, since no
point of first coordinate `a` is selected.

Assume it holds for `r+1`.  If no point of first coordinate `r` is selected,
then

```text
p^a - S_r = p^a - S_{r+1} = p^(r+1) X_{r+1}
           = p^r (p X_{r+1}),
```

and the new coefficient is positive.

If the selected point of first coordinate `r` is `(r,j)`, then

```text
p^a - S_r = p^r (p X_{r+1} - q^j).
```

It remains to see that the coefficient is positive.  The congruence modulo
`q^M`, together with the antichain property, implies `q^j | X_{r+1}`: all
terms with smaller first coordinate have second coordinate strictly larger
than `j`, the selected term has exactly the factor `q^j`, and `p` is coprime
to `q`.  Since `X_{r+1} > 0`, this gives `q^j <= X_{r+1}`.  Therefore

```text
p X_{r+1} - q^j >= (p-1) X_{r+1} > 0.
```

Thus the invariant reaches `r=0`.  At `r=0`,

```text
p^a - S = X_0 > 0.
```

But the original congruence also gives `q^M | (p^a - S)`.  Since

```text
0 < p^a - S <= p^a < q^M,
```

this is impossible.  The case `t<a` cannot occur, completing the proof.

## Embedding a smaller obstruction

The synchronization lemma lets one turn a small nonrepresentable integer into
larger nonrepresentable integers.

**Lemma 2.**  Let `c` be `(p,q)`-nonrepresentable and coprime to `p*q`.  Suppose
`a,M >= 1` satisfy

```text
p^a < q^M
c q^M < (p-1) p^a.
```

Then

```text
N = p^a + c q^M
```

is `(p,q)`-nonrepresentable and coprime to `p*q`.

**Proof.**  The second inequality gives

```text
N = p^a + c q^M < p^a + (p-1)p^a = p^(a+1).
```

So in any representation of `N`, every selected term has first coordinate at
most `a`.

Assume, for contradiction, that `N` is represented by an antichain `A`.  Split
`A` into the low part with second coordinate `< M` and the high part with
second coordinate `>= M`.  Reducing the representation modulo `q^M`, the low
part satisfies

```text
sum_low p^i q^j == p^a  (mod q^M).
```

The low part lies in `{0,...,a} x {0,...,M-1}`, so Lemma 1 forces the low part
to be exactly `{(a,0)}`.

Subtracting this term from the representation gives

```text
c q^M = sum_high p^i q^j.
```

Every high term has `j >= M`, so division by `q^M` gives

```text
c = sum_high p^i q^(j-M).
```

Shifting all high points down by `M` in the second coordinate preserves the
antichain condition.  Thus this is a valid representation of `c`, contradicting
the choice of `c`.

For coprimality, let `r` be a prime divisor of `q`.  Then

```text
N == p^a  (mod r),
```

which is nonzero because `gcd(p,q)=1`.  If `r` divides `p`, then

```text
N == c q^M  (mod r),
```

which is nonzero because `gcd(c,p*q)=1` and `gcd(p,q)=1`.  Hence
`gcd(N,p*q)=1`.

## Choosing synchronized exponents

For the construction we need `a` and `M` to be divisible by a prescribed
integer `L`, while keeping `q^M` only slightly larger than `p^a`.

**Lemma 3.**  Let `p,q > 1` be coprime, and let `rho > 1`.  For every positive
integer `L`, there exist positive multiples `a,M` of `L` such that

```text
1 < q^M / p^a < rho.
```

**Proof.**  Let

```text
alpha = log(p) / log(q).
```

This number is irrational; otherwise `alpha=r/s` would imply `p^s=q^r`,
impossible for coprime `p,q>1`.  The fractional parts of `n alpha` are dense in
`[0,1]`.  Choose `n` so that `n alpha` lies just below an integer, with the gap
less than `log(rho)/(L log q)`.  Put

```text
a = L n,
M = L ceil(n alpha).
```

Then

```text
0 < M - a alpha < log(rho)/log(q),
```

which is equivalent to

```text
1 < q^M / p^a < rho.
```

## Fresh extensions

Now suppose `c` satisfies the following seed conditions:

```text
c > 0,
c < p-1,
c is (p,q)-nonrepresentable,
gcd(c,p*q)=1,
every prime divisor of c+1 divides p*q.
```

We show that these conditions imply infinitely many pairwise-coprime
nonrepresentables.

Let `D` be any positive integer coprime to `p*q`; in the recursive construction
`D` will be the product of the previously constructed terms.  By Euler's
theorem, or by the elementary finite-order argument modulo `D`, there is a
positive integer `L` such that every multiple `e` of `L` satisfies

```text
p^e == 1  (mod D),
q^e == 1  (mod D).
```

Apply Lemma 3 with

```text
rho = (p-1)/c > 1.
```

Choose positive multiples `a,M` of `L` such that

```text
1 < q^M / p^a < (p-1)/c.
```

Equivalently,

```text
p^a < q^M
c q^M < (p-1)p^a.
```

Define

```text
N = p^a + c q^M.
```

By Lemma 2, `N` is `(p,q)`-nonrepresentable and coprime to `p*q`.  Since
`a` and `M` are multiples of `L`,

```text
N == 1 + c  (mod D).
```

Every prime divisor of `c+1` divides `p*q`, while `D` is coprime to `p*q`.
Hence `gcd(c+1,D)=1`, and therefore `gcd(N,D)=1`.

This proves the fresh-extension property: given any finite product `D` of
previous terms, we can construct a new nonrepresentable `N` coprime to `p*q`
and also coprime to `D`.

Starting with `D=1` and iterating this extension gives a sequence
`N_0,N_1,N_2,...`.  At stage `s`, take `D=N_0...N_{s-1}`.  The construction
ensures that `N_s` is coprime to `D`, hence to every previous `N_i`.  Thus the
sequence is pairwise coprime, and every term is nonrepresentable and coprime to
`p*q`.

## The three seeds

It remains to verify the seed conditions in the three exceptional cases.

We use the elementary observation:

**Lemma 4.**  If `0 < c < p` and `c` is not a power of `q`, then `c` is
`(p,q)`-nonrepresentable.

Indeed, any selected term at most `c` must have first coordinate `0`, since
any term with positive first coordinate is at least `p`.  Terms with first
coordinate `0` are powers of `q`, and among them the antichain condition permits
at most one.  Thus a representation of `c` would force `c=q^j` for some `j`.

Now check the cases.

For `(p,q)=(5,2)`, take `c=3`.  Then

```text
0 < 3 < 4 = p-1,
gcd(3,10)=1,
3 is not a power of 2,
c+1=4 has only the prime divisor 2, which divides 10.
```

For `(p,q)=(9,2)`, take `c=5`.  Then

```text
0 < 5 < 8 = p-1,
gcd(5,18)=1,
5 is not a power of 2,
c+1=6 has prime divisors 2 and 3, both dividing 18.
```

For `(p,q)=(5,3)`, take `c=2`.  Then

```text
0 < 2 < 4 = p-1,
gcd(2,15)=1,
2 is not a power of 3,
c+1=3 divides 15.
```

Each seed satisfies the conditions above.  Therefore each of the three pairs
has infinitely many pairwise-coprime `(p,q)`-nonrepresentable positive
integers, with each constructed integer also coprime to `p*q`.

## Formal endpoints

The Lean theorem names corresponding to the three unconditional exceptional
cases are:

```lean
#check Erdos1110.exceptional_5_2_unconditional
#check Erdos1110.exceptional_9_2_unconditional
#check Erdos1110.exceptional_5_3_unconditional
```

They have types:

```text
∃ f, Erdos1110.PairwiseCoprimeNonrepSeq 5 2 f
∃ f, Erdos1110.PairwiseCoprimeNonrepSeq 9 2 f
∃ f, Erdos1110.PairwiseCoprimeNonrepSeq 5 3 f
```

The bridge theorem

```lean
#check Erdos1110.erdos1110_from_yuChen
```

packages these exceptional cases with an explicit Yu-Chen range hypothesis.
The Yu-Chen theorem itself is not formalized in this repository.

## References

- P. Erdős and M. Lewin, *d-Complete Sequences of Integers*, Mathematics of
  Computation 65 (1996), 837-840.  A public PDF mirror is available at
  <https://brand.site.co.il/riddles/201507a_files/2153618.pdf>.
- W.-X. Yu and Y.-G. Chen, *On a conjecture of Erdős and Lewin*, Journal of
  Number Theory 238 (2022), 763-778.  DOI:
  <https://doi.org/10.1016/j.jnt.2021.09.018>.
