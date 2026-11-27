# A proof of Kimberling's inequality for Archimedean copulas with completely monotone generators

Ming-Chih Kao (Stanford University). 26 November 2026.

The proof and its formalization were developed with AI assistance (Claude, with independent reviews by
other models); the author is responsible for the content. A complete Lean 4 formalization of Theorem 1 accompanies this note (`Kimberling/Basic.lean`, theorem
`Kimberling.main`). It uses the Hausdorff–Bernstein–Widder theorem of the TauCeti library; §5 has the details.

## 1. Statement

Let f : [0, ∞) → ℝ satisfy:

- (H1) f is continuous on [0, ∞), f(0) = 1, and f(x) → 0 as x → ∞;
- (H2) f is completely monotone on (0, ∞): f ∈ C^∞(0, ∞) and (−1)^k f^{(k)}(x) ≥ 0 for all k ≥ 0 and x > 0.

By Lemma 2 below, every u ∈ (0, 1] has a preimage under f in [0, ∞). Write g(u) ∈ [0, ∞) for a chosen
preimage, so that f(g(u)) = u.
- In fact f is strictly decreasing, so g is the inverse of f, but the proof never uses this.
- Set g(0) = ∞ and f(∞) = 0.

Define the Archimedean copula

  C(u, v) = f(g(u) + g(v)) for u, v ∈ (0, 1],  and C(u, v) = 0 if u = 0 or v = 0.

**Theorem 1.** For all u, v ∈ [0, 1], with a = (u + v)/2,

  C(a, a) − a² ≥ C(u, v) − uv.

This answers the question of C. Kimberling (MathOverflow 195959, 2015), read with the source's convention that C is
an Archimedean copula. There, f maps [0, ∞] onto [0, 1] and is completely monotone on (0, ∞).
- *What those hypotheses force.* Surjectivity together with complete monotonicity (hence continuity and monotonicity
  on (0, ∞)) forces the interior limits f(0+) = 1 and f(∞−) = 0.
- *What they do not force.* They do not by themselves fix the endpoint values: the swapped assignment f(0) = 0,
  f(∞) = 1 is also a bijection, but it gives C(0, v) = v, which is not a copula.
- *The reading used here.* The source's statement that C is an Archimedean copula selects f(0) = 1, f(∞) = 0 with f
  continuous on [0, ∞]. That is exactly (H1).

The Lean statement `statements/mo-195959.lean` (PR #1260) explains this reading in its docstring, and its hypotheses
are (H1)–(H2) verbatim:
- `CompletelyMonotoneOn f (Ioi 0)` uses `iteratedDerivWithin` on the open set (0, ∞), which agrees there with ordinary
  derivatives.
- For u ∈ (0, 1], `Function.invFunOn f (Ici 0) u` is the unique preimage given by Lemma 2.

The MathOverflow answers proved the inequality for the Clayton family f(x) = (1 + x)^{−1/t} with t ≥ 1.

Theorem 2 (§3b) strengthens Theorem 1. For strict Archimedean copulas it needs only stochastic increasingness
(SI), and it shows that C(u, v) − uv is Schur-concave.

## 2. Three lemmas

**Lemma 1 (Bernstein–Widder).** If f is completely monotone on (0, ∞), there is a unique positive Borel measure μ
on [0, ∞) with f(s) = ∫_{[0,∞)} e^{−sλ} μ(dλ) < ∞ for every s > 0. In particular μ is locally finite.
(Bernstein 1929; Widder, *The Laplace Transform*, 1941 (2nd printing 1946), Ch. IV; Schilling–Song–Vondraček, *Bernstein Functions*,
2nd ed., 2012, Thm 1.4.)

**Lemma 2 (normalization).** Under (H1)–(H2), μ is a probability measure. With Λ ~ μ and X := e^{−Λ} ∈ (0, 1],

  f(s) = E[X^s] for every s ∈ [0, ∞).   (1)

Moreover, every u ∈ (0, 1] equals f(x) for some x ≥ 0.

*Proof.*
- **Total mass.** Take a sequence s_n ↓ 0. Then e^{−s_nλ} increases to 1 for each λ ≥ 0. By monotone
  convergence, μ([0, ∞)) = lim_n f(s_n) = f(0) = 1, using continuity of f at 0 from (H1). So μ is a probability
  measure, (1) also holds at s = 0, and Λ < ∞, so X ∈ (0, 1].
- **Preimages.** Given u ∈ (0, 1], pick T ≥ 0 with f(T) < u, possible because f → 0. By the intermediate value
  theorem on [0, T] (f is continuous, f(0) = 1 ≥ u), some x ∈ [0, T] has f(x) = u. ∎

The proof below needs neither μ({0}) = 0 nor strict monotonicity of f, although both hold under (H1)–(H2).

For u, v ∈ (0, 1], (1) gives
  C(u, v) = f(g(u) + g(v)) = E[X^{g(u)} X^{g(v)}],
which is the frailty (mixture) representation of Marshall and Olkin (1988, Thm 2.1 and Cor. 2.2). That f is
completely monotone exactly when it generates an Archimedean copula in every dimension is due to Kimberling (1974);
see also Nelsen (2006, Thm 4.6.2).

**Lemma 3 (single crossing).** Let ν be a probability measure on an interval I ⊂ ℝ. Let h, w : I → ℝ be bounded
Borel functions with ∫ h dν = 0, and w nondecreasing. Suppose P := {t ∈ I : h(t) ≥ 0} is nonempty and is an upper
set: t ∈ P and t′ ≥ t imply t′ ∈ P. Then ∫ h w dν ≥ 0.

*Proof.*
- **Threshold value.** Let κ := inf w(P). The set is nonempty, and bounded below whenever w is bounded.
- **Points of P.** For t ∈ P we have h(t) ≥ 0 and w(t) ≥ κ.
- **Points outside P.** For t ∉ P, every t′ ∈ P satisfies t′ > t, since otherwise t ∈ P because P is an upper set.
  So w(t) ≤ w(t′) for all t′ ∈ P, that is, w(t) ≤ κ, while h(t) < 0.
- **Integrate.** In both cases h(t)(w(t) − κ) ≥ 0. Integrating, ∫ h w dν ≥ κ ∫ h dν = 0. ∎

This is the cut criterion of Karlin and Novikoff (1963) in its simplest form. The formulation with κ = inf w(P)
avoids locating the crossing point, and it is the one used in the Lean proof.

## 3. Proof of Theorem 1

The inequality and C are symmetric in (u, v), and u = v gives equality. So assume u ≠ v.

**Case 1: one argument is 0, say v = 0 < u.**
- Then C(u, v) − uv = 0, and a = u/2 ∈ (0, 1/2]. Put z = g(a) ≥ 0.
- By (1), C(a, a) − a² = f(2z) − f(z)² = E[X^{2z}] − (E[X^z])² = Var(X^z) ≥ 0.

**Case 2: u, v ∈ (0, 1], u ≠ v.**
- **Exponents.** Put x = g(u), y = g(v), z = g(a), all in [0, ∞). No ordering of x, y, z is needed.
- **Random variables.** Define p_u = X^x, p_v = X^y, p_a = X^z and q = (p_u + p_v)/2, all with values in (0, 1].
- **Moments.** By (1), E p_u = u, E p_v = v, and E p_a = a = E q.
- **Covariance and variance.** C(u, v) = f(x + y) = E[p_u p_v] and C(a, a) = f(2z) = E[p_a²]. Hence
  - C(u, v) − uv = Cov(p_u, p_v);
  - C(a, a) − a² = Var(p_a).   (2)
- **Step A: Var(q) ≥ Cov(p_u, p_v).** Expanding,
  Var(q) − Cov(p_u, p_v) = ¼ Var(p_u − p_v) ≥ 0.
- **Step B: Var(p_a) ≥ Var(q).**
  - *Reduction.* Since E p_a = E q, Var(p_a) − Var(q) = E[h(X) w(X)], with
    h(t) = t^z − (t^x + t^y)/2 and w(t) = t^z + (t^x + t^y)/2 on I = (0, 1].
  - *w is nondecreasing*, as all exponents are ≥ 0. E h(X) = 0, and h(1) = 0, so 1 ∈ P.
  - *P is an upper set.* For t ∈ (0, 1] write L = log t ≤ 0. Then h(t) = t^z (1 − s(L)/2) with
    s(L) = e^{(x−z)L} + e^{(y−z)L}. So h(t) ≥ 0 ⇔ s(L) ≤ 2.
  - *Convexity.* s is convex (a sum of exponentials, whatever the signs of x − z and y − z) and s(0) = 2. So if
    L ≤ L′ ≤ 0 and s(L) ≤ 2, writing L′ = θL with θ ∈ [0, 1] gives s(L′) ≤ θ s(L) + (1 − θ) s(0) ≤ 2.
  - *Apply Lemma 3* with ν the law of X. It gives E[h(X) w(X)] ≥ 0.
- **Conclusion.** By (2), Step B and Step A,
  C(a, a) − a² = Var(p_a) ≥ Var(q) ≥ Cov(p_u, p_v) = C(u, v) − uv. ∎

## 3b. A stronger theorem under stochastic increasingness

**Theorem 2.** Let f : [0, ∞) → (0, 1] be continuous, with f(0) = 1, f → 0, and continuously differentiable on
(0, ∞). Suppose b := −f′ > 0 is log-convex on (0, ∞). Equivalently, the strict Archimedean copula C is SI, that is,
stochastically increasing (Müller–Scarsini 2005, Thm 2.8; Fuchs–Tschimpke 2023, Thm 1; see also Nelsen 2006,
Ex. 5.34, citing Capéraà–Genest 1993). Then for each a ∈ (0, 1), the map
t ↦ C(a + t, a − t) − (a + t)(a − t) is non-increasing on [0, min(a, 1 − a)]. So C − Π is Schur-concave on
[0, 1]². In particular C(a, a) − a² ≥ C(u, v) − uv.

Here C is defined from f as in §1.

Complete monotonicity implies the hypothesis. Since f → 0 forces μ({0}) = 0, we have Λ > 0 a.s., so
b(s) = E[Λe^{−sΛ}] > 0, and b is log-convex by Cauchy–Schwarz, as in
Müller–Scarsini 2005, Thm 2.14. So Theorem 2 contains Theorem 1. The argument below was suggested in one of the AI reviews
of this note. We checked it by hand and numerically.

*Proof.*
- **Setting.** By positivity of b and the fundamental theorem of calculus on [ε, M], ∫₀^∞ b = f(0) − f(∞) = 1. So b
  is integrable. A positive, integrable, log-convex function on (0, ∞) is strictly decreasing: if
  log b(s₂) ≥ log b(s₁) with s₁ < s₂, convexity gives b ≥ b(s₂) > 0 on [s₂, ∞). Hence f′ = −b is increasing, f is
  convex, and f generates a strict Archimedean copula.
- **Derivative along the anti-diagonal.** Fix a and 0 < t < min(a, 1 − a). Put u = a + t, v = a − t,
  x = g(u) < y = g(v). Since g′(u) = −1/b(g(u)),
  d/dt [C(a + t, a − t) − (a² − t²)] = 2t − b(x + y)·(1/b(y) − 1/b(x)).
  We must show b(x + y)(1/b(y) − 1/b(x)) ≥ 2t = u − v = f(x) − f(y) = ∫_x^y b.
- **Comparison exponential.** Let ℓ(s) = A e^{−rs} agree with b at x and y.
  - r ≥ 0 because b is non-increasing.
  - r > 0: if r = 0, convexity of log b would force b ≥ b(y) on [y, ∞), contradicting integrability.
  - Log-convexity gives b ≤ ℓ on [x, y] and b ≥ ℓ outside [x, y].
- **Mass inside [x, y].** Put α = ∫_x^y b and β = 1 − α = ∫ outside b. Then ∫_x^y ℓ ≥ α and ∫ outside ℓ ≤ β.
  Hence αQ ≤ βP, where P = ∫_x^y ℓ and Q = ∫ outside ℓ. So
  α = α/(α + β) ≤ P/(P + Q) = e^{−rx} − e^{−ry}.
- **The derivative is ≤ 0.** x + y ≥ y gives b(x + y) ≥ ℓ(x + y). Hence
  b(x + y)(1/b(y) − 1/b(x)) ≥ ℓ(x + y)(1/ℓ(y) − 1/ℓ(x)) = e^{−rx} − e^{−ry} ≥ α.
- **Endpoints.** C is continuous, so monotonicity extends to the closed interval, including arguments equal to 0
  or 1. In two dimensions, for a fixed sum u + v, majorization is exactly the ordering by |u − v|. So, by symmetry,
  this is Schur-concavity of C − Π. ∎

**Numerical check.** For 200 random log-convex b that are not completely monotone, the largest observed forward
increment (as t increases) of t ↦ C(a + t, a − t) − (a² − t²) on a grid was at most 10⁻⁷.

**Theorem 2 needs the Archimedean structure.** Remark 3 shows that SI cannot be weakened to LTD = TP2(C) within the
Archimedean class. The Archimedean structure itself is also needed: symmetry and SI alone do not imply even the
midpoint inequality. One of the AI reviews of this note gave this example:
- *The copula.* Put p(s) = min(3s, 1 − s), q(s) = min(s, 3(1 − s)), and C(u, v) = uv + [p(u)q(v) + q(u)p(v)]/20.
- *Its properties.* The margins are uniform. The density is ≥ 1 − 18/20 > 0, since |p′|, |q′| ≤ 3. C is symmetric,
  and it is SI because p and q are nonnegative and concave.
- *The violation.* On [1/4, 3/4], (C − Π)(1/2 + t, 1/2 − t) = (1/2 + 2t²)/20, which increases in t. So at
  (u, v) = (3/4, 1/4), C(a, a) − a² = 0.025 < 0.03125 = C(u, v) − uv. We checked this numerically.

Even density-TP2 together with symmetry is not enough. Another review gave the 3 × 3 checkerboard copula with
density 3P_{ij} on the cells of the uniform 3 × 3 grid, where P = [[5/8, 3/8, 0], [3/8, 1/4, 3/8], [0, 3/8, 5/8]].
- *Its properties.* P is symmetric and doubly stochastic, and every 2 × 2 minor is ≥ 1/64 > 0, so the density is TP2.
- *The violation (exact rational arithmetic).* C(1/2, 1/2) − 1/4 = 5/48 < 1/9 = C(2/3, 1/3) − 2/9.

**Why Archimedean structure matters.** For a symmetric C² copula, the second derivative of
t ↦ C(a + t, a − t) − (a² − t²) at t = 0 is 2(1 − c(a, a) + ∂₁₁C(a, a)), where c is the density. In the Archimedean
case c − ∂₁₁C equals the ratio of Remark 4, which is forced to be ≥ 1.


## 4. Remarks

1. **Decomposition.** For u, v ∈ (0, 1] the proof gives
   Δ := C(a,a) − a² − C(u,v) + uv = [Var p_a − Var q] + ¼ Var(p_u − p_v),
   a sum of two nonnegative terms. The same single crossing gives the convex order q ≤_cx p_a.
   - *Why.* For convex φ : ℝ → ℝ, φ(p_a) − φ(q) ≥ φ′₊(q)(p_a − q), and t ↦ φ′₊(q(t)) is nondecreasing on (0, 1].
   - *Conclusion.* So Lemma 3 with w = φ′₊ ∘ q gives E φ(p_a) ≥ E φ(q). This is the Karlin–Novikoff cut criterion
     for the comonotone pair p_a, q.
   - *Scope.* Only the case φ(t) = t² is used in the Theorem.
2. **Equality cases.** These are not needed for the Theorem, and we make no claim about them here.
3. **Complete monotonicity cannot be weakened to PQD, LTD, or TP2 of the copula function.** Take f = e^{−φ} with φ(x) = 10x on [0, 0.1] and
   φ(x) = 1 + 0.1(x − 0.1) afterwards.
   - *It is a PQD Archimedean copula.* φ is increasing and concave with φ(0) = 0, hence subadditive, so
     f(x+y) ≥ f(x)f(y) and C is PQD. f is log-convex, hence convex, so it is a valid strict bivariate generator.
     f is not C¹ at 0.1. A concave smoothing of φ near 0.1 keeps φ increasing and concave. So it preserves every
     property listed here (PQD, LTD, TP2(C), LCSD) and keeps Δ < 0, since none of the evaluation points
     g(u), g(v), g(a), 2g(a), g(u) + g(v) equals 0.1.
   - *It violates the inequality.* At u = 11/30, v = 25/30 (so a = 3/5),
     Δ = e^{−0.99}(3/5)^{0.02} − (11/30)(5/6)^{0.01} − 49/900 = −0.05264… (checked at 50 digits and in closed form).
   - *It is also LTD.* With s = g(u), t = g(v), C(u, v)/u = exp(−[φ(s + t) − φ(s)]). The increment of a concave φ
     is non-increasing in s, and s decreases as u increases, so C(u, v)/u is non-increasing in u. Hence the copula
     function C is TP2, equivalently LCSD, because LTD ⇔ TP2 of C for Archimedean copulas (Fuchs–Tschimpke 2023,
     p. 164; Nelsen 2006, Ex. 5.34). This is TP2 of C itself, not of its density.
   - *Schur-concavity does not explain it either.* Every Archimedean copula is Schur-concave (Nelsen 2006,
     Ex. 4.13, after Durante–Sempi 2003), and this example is Archimedean.
   - *It is not SI.* Fix 0 < y < 0.1. As x increases through 0.1 − y, the conditional ratio b(x + y)/b(x) jumps
     down, while b(x) is continuous there. This contradicts the monotonicity that SI requires, however a derivative
     at the corner is defined. Theorem 2 shows that SI suffices. So along the Archimedean chain
     d-TP2 ⇒ SI ⇒ TP2(C) ⇔ LTD ⇒ PQD, the inequality holds from SI upward and can fail at TP2(C)/LTD.
4. **Infinitesimal form.** Near the diagonal, Δ ≈ (u − v)²·(|f′(2x)| f″(x)/|f′(x)|³ − 1)/4 with x = g(a). The
   bracket is ≥ 0 by Hölder's inequality with exponents (3, 3, 3) applied to (1).
5. **Numerical checks.** The decomposition in Remark 1 was verified at 40 digits for 3000 random mixtures of 1–4
   exponentials (agreement to 10⁻³⁰; both brackets ≥ 0). We also checked these families on 400² grids, in their
   completely monotone parameter ranges:
   - Clayton (1 + x)^{−1/t} with t ∈ [0.01, 5], including t < 1;
   - Gumbel θ ≥ 1;
   - Frank θ > 0;
   - AMH θ ∈ [0, 1);
   - Joe θ ≥ 1.

## 5. Formal verification

Theorem 1 is formalized in Lean 4 as `Kimberling.main` (file `Kimberling/Basic.lean`, about 400 lines), and it
builds with no `sorry`.
- **Toolchain.** Lean v4.37.0-rc1 with Mathlib, as pinned by TauCeti. This is a standalone project. It is not
  checked by the Left to Solve CI, which runs Lean v4.33.1 without TauCeti.
- **Theorem 2 is not formalized.**
- **Bernstein's theorem.** Taken from TauCeti (Apache-2.0, commit ac8801f6):
  `TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi`.
- **Axioms.** `#print axioms Kimberling.main` reports only `propext`, `Classical.choice` and `Quot.sound`.
- **Statement.** The definitions `CompletelyMonotoneOn` and `archC` and the statement of `main` are copied verbatim
  from the Left to Solve statement `mo-195959` (PR #1260 of open-math-agents). In particular g is
  `Function.invFunOn f (Set.Ici 0)`, which is exactly the "chosen preimage" of §1.

## 6. Relation to the literature

We found no earlier proof of Theorem 1 or Theorem 2, in the stated generality, in the sources examined:
- Kimberling 1973 and 1974;
- Nelsen 2006: Ch. 4 including all exercises, §3.4 and §5.2;
- Durante–Sempi 2003 and 2016 (§6.5);
- Müller–Scarsini 2005;
- Marshall–Olkin 1988;
- Fuchs–Tschimpke 2023;
- forward citations of these works, screened by title in OpenAlex.

**How the methods relate to known work.** Theorem 1 is, in method, an application of the classical single-crossing
(cut) criterion for convex order (Karlin–Novikoff 1963; Ohlin 1969) to the frailty representation of Marshall and
Olkin (1988). What is specific to this problem is the verification of the single crossing, by convexity of a sum of
exponentials.

**Nearest structural result.** Among the sources examined, the nearest structural result is Schur-concavity of
every Archimedean copula (Durante–Sempi 2003, Thm 4). It does not imply Theorem 1: Π is also Schur-concave, and the
Archimedean example of Remark 3 violates the inequality. Theorem 2 does not extend to all symmetric SI copulas, or even to symmetric
density-TP2 copulas (§3b).

Limitations:
- We could not consult Joe (2014).
- We did not search MathSciNet, zbMATH or Google Scholar.
- We did not systematically screen the stochastic-orders literature (e.g. Shaked–Shanthikumar).

We therefore claim only that we found no prior proof. Pointers are welcome.

## References

- S. Bernstein, Sur les fonctions absolument monotones, Acta Math. 52 (1929) 1–66.
- P. Capéraà, C. Genest, Spearman's ρ is larger than Kendall's τ for positively dependent random variables,
  J. Nonparametr. Statist. 2 (1993) 183–194.
- F. Durante, C. Sempi, Copulæ and Schur-concavity, Int. Math. J. 3 (2003) 893–905.
- F. Durante, C. Sempi, Principles of Copula Theory, CRC Press, 2016.
- S. Fuchs, M. Tschimpke, On positive dependence properties for Archimedean copulas, in: Building Bridges between
  Soft and Statistical Methodologies for Data Science (SMPS 2022), AISC 1433, Springer, 2023, pp. 159–165.
- S. Karlin, A. Novikoff, Generalized convex inequalities, Pacific J. Math. 13 (1963) 1251–1279.
- C. H. Kimberling, Two-dimensional complete monotonicity with diagonalization, Amer. Math. Monthly 80 (1973) 789–791.
- C. H. Kimberling, A probabilistic interpretation of complete monotonicity, Aequationes Math. 10 (1974) 152–164.
- C. H. Kimberling, An inequality for copulas, MathOverflow question 195959 (2015), https://mathoverflow.net/q/195959.
- A. W. Marshall, I. Olkin, Families of multivariate distributions, J. Amer. Statist. Assoc. 83 (1988) 834–841.
- A. Müller, M. Scarsini, Archimedean copulae and positive dependence, J. Multivariate Anal. 93 (2005) 434–445.
- R. B. Nelsen, An Introduction to Copulas, 2nd ed., Springer, 2006.
- J. Ohlin, On a class of measures of dispersion with application to optimal reinsurance, ASTIN Bull. 5 (1969)
  249–266.
- R. L. Schilling, R. Song, Z. Vondraček, Bernstein Functions, 2nd ed., de Gruyter, 2012.
- TauCeti Project, TauCeti (Lean 4 library), https://github.com/TauCetiProject/TauCeti, commit ac8801f6.
- D. V. Widder, The Laplace Transform, Princeton University Press, 1941 (second printing 1946).
