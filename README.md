# Kimberling's copula inequality (MathOverflow 195959), formalized in Lean 4

`Kimberling.main` proves the following. Let `f` be continuous on `[0, ∞)` with `f 0 = 1` and `f → 0`, and completely
monotone on `(0, ∞)`. Let `C(u, v) = f(g(u) + g(v))`, where `g` is the inverse of `f`. Then for all `u, v` in `[0, 1]`,
with `a = (u + v)/2`,

    C(a, a) - a² ≥ C(u, v) - uv.

This answers a question posed by Clark Kimberling on MathOverflow (195959, 2015).

The definitions and the statement are copied verbatim from the Left to Solve statement `mo-195959`. The source checks
that they are identical.

## How the proof goes

1. **Bernstein's theorem.** `f` is the Laplace transform of a probability measure `μ` on `ℝ≥0`. This is
   `TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi` from
   [TauCeti](https://github.com/TauCetiProject/TauCeti), pinned at commit `ac8801f6`.
2. **Covariance form.** Write `E c x = exp (-(c x))`. Then `C(u, v) - uv = Cov(E g(u), E g(v))` and
   `C(a, a) - a² = Var(E g(a))`.
3. **Single crossing.** `Var(E g(a)) ≥ Var((E g(u) + E g(v))/2)`.
4. **Variance of a difference.** `Var((E g(u) + E g(v))/2) ≥ Cov(E g(u), E g(v))`.

The informal write-up is in `work/kimberling/note.md` in the parent workspace.

## Build

Lean `v4.37.0-rc1`, using Mathlib through TauCeti's manifest.

    lake exe cache get
    lake build
    lake env lean scripts/Axioms.lean   # prints [propext, Classical.choice, Quot.sound]
