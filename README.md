# Kimberling's inequality for Archimedean copulas: proof and Lean 4 formalization

## The theorem

Let f : [0, ∞) → ℝ satisfy two conditions:
- f is continuous, f(0) = 1, and f(x) → 0 as x → ∞;
- f is completely monotone on (0, ∞), that is, (−1)^k f^{(k)} ≥ 0 for all k.

Let g be an inverse of f on (0, 1] (it exists, and f is strictly decreasing), and C(u, v) = f(g(u) + g(v)), with C = 0 when u = 0 or v = 0. Then for all
u, v ∈ [0, 1], with a = (u + v)/2,

    C(a, a) − a² ≥ C(u, v) − uv.

This answers a question posed by Clark Kimberling on [MathOverflow 195959](https://mathoverflow.net/q/195959)
(2015), read with the usual Archimedean convention f(0) = 1, f(∞) = 0. There it was proved only for the Clayton
generators f(x) = (1 + x)^{−1/t} with t ≥ 1. This statement (Theorem 1) is machine-checked in Lean.

NOTE.md also proves a stronger statement on paper (Theorem 2, not formalized). For strict Archimedean copulas it needs
only that −f′ is log-convex, which is equivalent to the copula being stochastically increasing (SI). The
Archimedean structure matters: NOTE.md §3b gives symmetric non-Archimedean copulas, one SI and one even with a TP2
density, for which the inequality fails. Under that condition C(u, v) − uv is
Schur-concave: it is non-increasing as one moves away from the diagonal along every line u + v = const.

## Proof sketch (Theorem 1)

The full proofs are in [NOTE.md](NOTE.md).

1. **Bernstein's theorem.** f(s) = E[X^s] for a random variable X ∈ (0, 1]. Then
   C(u, v) = E[X^{g(u)} X^{g(v)}], which is the frailty representation of Marshall and Olkin (1988).
2. **Covariance form.** With p_u = X^{g(u)}, the two sides are C(u, v) − uv = Cov(p_u, p_v) and
   C(a, a) − a² = Var(p_a).
3. **Step A.** Var((p_u + p_v)/2) − Cov(p_u, p_v) = ¼ Var(p_u − p_v) ≥ 0.
4. **Step B (single crossing).** Var(p_a) ≥ Var((p_u + p_v)/2). Both variables have mean a. Their difference
   h(X) = X^{g(a)} − (X^{g(u)} + X^{g(v)})/2 has nonnegative set {h ≥ 0} that is an upper set in X: the ratio
   (t^x + t^y)/(2t^z) is a convex function of log t equal to 1 at t = 1. The classical Karlin–Novikoff (Ohlin)
   single-crossing criterion for convex order then finishes. Methodologically, Theorem 1 is an application of that
   criterion to the frailty representation.

The note's Remark 3 gives an explicit Archimedean copula that violates the inequality. It is positively quadrant
dependent, left-tail decreasing, and TP2 as a function (equivalently LCSD; not density-TP2), but it is not SI. So along
the Archimedean chain density-TP2 ⇒ SI ⇒ TP2(C) ⇔ LTD ⇒ PQD, the inequality holds from SI upward and can fail
below.

## Lean formalization

`Kimberling/Basic.lean` proves `Kimberling.main`, which is Theorem 1. It builds with no `sorry`:

    $ lake env lean scripts/Axioms.lean
    'Kimberling.main' depends on axioms: [propext, Classical.choice, Quot.sound]

**The statement matches Left to Solve exactly.** The definitions `CompletelyMonotoneOn` and `archC` and the
statement of `main` are copied verbatim from the Left to Solve statement `mo-195959`, the formalization of
MathOverflow 195959 submitted as PR #1260 to
[open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents).
- Complete monotonicity is `ContDiffOn ℝ ⊤ f (Ioi 0)` together with the sign conditions on `iteratedDerivWithin`.
- g is `Function.invFunOn f (Set.Ici 0)`.

**Bernstein's theorem is used from the [TauCeti](https://github.com/TauCetiProject/TauCeti) library.**
- TauCeti is licensed Apache-2.0 and pinned at commit `ac8801f612041ee3dcb3fa3f950f01318206737c`.
- The theorem used is `TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi`, the
  Hausdorff–Bernstein–Widder theorem.
- We thank the TauCeti authors. This project would not be feasible without their formalization.

The rest of the file (about 400 lines in all) is elementary measure theory:
- the variance inequality;
- the single-crossing lemma, which uses κ = inf w(P) instead of locating the crossing point;
- existence of preimages by the intermediate value theorem;
- the case analysis for `archC`.

### Build

Requirements: [elan](https://github.com/leanprover/elan).
- The toolchain `leanprover/lean4:v4.37.0-rc1` is installed automatically. This pin is inherited from TauCeti.
- This is a standalone project. It is not part of the Left to Solve CI, which runs an older Lean without TauCeti.
- Disk: about 9 GB for the Mathlib cache.

    lake exe cache get        # downloads the prebuilt Mathlib
    lake build                # builds the needed TauCeti modules and Kimberling
    lake env lean scripts/Axioms.lean

## Novelty

We found no earlier proof of Theorem 1 or Theorem 2, in the stated generality, in the literature we examined:
- Kimberling 1973 and 1974;
- Nelsen, *An Introduction to Copulas* (2006), Ch. 4 and §5.2;
- Durante–Sempi 2003 (*Copulæ and Schur-concavity*) and 2016 (*Principles of Copula Theory*, §6.5);
- Müller–Scarsini 2005;
- Marshall–Olkin 1988;
- Fuchs–Tschimpke 2023;
- OpenAlex forward-citation screens.

Schur-concavity of Archimedean copulas (Durante–Sempi 2003) does not imply it, and neither do PQD, LTD or TP2(C)
(NOTE.md, Remark 3).

Limitations of the search:
- We could not consult Joe, *Dependence Modeling with Copulas* (2014).
- We did not search MathSciNet, zbMATH or Google Scholar.
- We did not systematically screen the stochastic-orders literature (e.g. Shaked–Shanthikumar).

So we claim only that we found no prior proof. Pointers to earlier work are welcome.

## Credits and license

- **Author:** Ming-Chih Kao (Stanford University).
- **AI tools:** the proofs and the formalization were developed with AI assistance (Claude, with independent reviews by
  other models; the SI argument of Theorem 2 and the two counterexamples in NOTE.md §3b came from such reviews). The author is responsible for the content.
- **Machine checking:** every step of Theorem 1 is checked by the Lean kernel.
- **License:** Apache-2.0 (see LICENSE). TauCeti and Mathlib are used under their Apache-2.0 licenses.
