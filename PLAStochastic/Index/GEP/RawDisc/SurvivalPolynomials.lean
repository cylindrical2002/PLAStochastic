import PLAStochastic.Index.GEP.RawDisc.ProductLaws
import Mathlib.Analysis.Complex.Liouville

/-!
# WP4 `RawDisc` assembly, part 2: the survival polynomials

`cSurv eps ν σ z k G = ∑_{S ⊆ {0,…,k-1}} (1-z)^{k-|S|} z^{|S|} α_S` (`PLAStochastic/Index/GEP/RawDisc/Defs.lean`) is a
polynomial in `z`:

* `differentiable_cSurv`: it is entire;
* `cSurv_zero`, `hasDerivAt_cSurv_zero`: its value at `0` is `α_∅ = ∫ G(S_k) 1{k<T} dν^∞`, its
  derivative at `0` is `-k α_∅ + ∑_{i<k} α_{{i}}` (only words with at most one `σ`-coordinate
  contribute);
* `cSurv_ofReal`: on the real segment `t ∈ [0,1]` it is the survival integral under the
  mixture product `((1-t)ν + tσ)^{⊗∞}` (word expansion, `integral_iidLaw_mix`);
* `abs_deriv_cSurv_le`: a bound `‖cSurv z‖ ≤ B` on `ball 0 r` bounds the linear coefficient by
  `2B/r` (Cauchy).  Applied to the positive test `e^{γ y/ε²}` this controls the survival
  integrals of the one-letter words `wordLaw ν σ {i}` through the survival bound itself.
* `occTerm`: the occupation terms `Ψ_k(z) = (1 - z) cSurv_k(G_ν) + z cSurv_k(G_σ)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ## Polynomials over words -/

/-- The word polynomial `∑_{S ⊆ {0,…,k-1}} (1-z)^{k-|S|} z^{|S|} c_S`. -/
def wordPoly (k : ℕ) (c : Finset ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ S ∈ (Finset.range k).powerset, (1 - z) ^ (k - S.card) * z ^ S.card * c S

theorem differentiable_wordPoly (k : ℕ) (c : Finset ℕ → ℂ) :
    Differentiable ℂ (wordPoly k c) := by
  unfold wordPoly
  fun_prop

theorem wordPoly_zero (k : ℕ) (c : Finset ℕ → ℂ) : wordPoly k c 0 = c ∅ := by
  unfold wordPoly
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · simp
  · intro S _ hS
    rw [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hS)), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

theorem hasDerivAt_wordPoly_zero (k : ℕ) (c : Finset ℕ → ℂ) :
    HasDerivAt (wordPoly k c) (-(k : ℂ) * c ∅ + ∑ i ∈ Finset.range k, c {i}) 0 := by
  classical
  have hterm : ∀ S : Finset ℕ, HasDerivAt
      (fun z : ℂ => (1 - z) ^ (k - S.card) * z ^ S.card * c S)
      (((if S.card = 0 then -(k : ℂ) else 0) + (if S.card = 1 then 1 else 0)) * c S) 0 := by
    intro S
    have h1 : HasDerivAt (fun z : ℂ => (1 - z) ^ (k - S.card))
        (((k - S.card : ℕ) : ℂ) * (1 - 0) ^ (k - S.card - 1) * (-1)) 0 :=
      ((hasDerivAt_id (0 : ℂ)).const_sub 1).pow (k - S.card)
    have h2 : HasDerivAt (fun z : ℂ => z ^ S.card)
        ((S.card : ℂ) * (0 : ℂ) ^ (S.card - 1)) 0 := hasDerivAt_pow S.card 0
    have h3 : HasDerivAt (fun z : ℂ => (1 - z) ^ (k - S.card) * z ^ S.card * c S)
        ((((k - S.card : ℕ) : ℂ) * (1 - 0) ^ (k - S.card - 1) * (-1) * (0 : ℂ) ^ S.card +
          (1 - 0) ^ (k - S.card) * ((S.card : ℂ) * (0 : ℂ) ^ (S.card - 1))) * c S) 0 :=
      (h1.mul h2).mul_const (c S)
    refine h3.congr_deriv ?_
    obtain h | h | h : S.card = 0 ∨ S.card = 1 ∨ 2 ≤ S.card := by omega
    · simp [h]
    · simp [h]
    · have hne0 : S.card ≠ 0 := by omega
      have hne1 : S.card ≠ 1 := by omega
      rw [if_neg hne0, if_neg hne1, zero_pow hne0,
        zero_pow (show S.card - 1 ≠ 0 by omega)]
      simp
  have hsum := HasDerivAt.fun_sum (u := (Finset.range k).powerset) fun S _ => hterm S
  have e : (fun z : ℂ => ∑ S ∈ (Finset.range k).powerset,
      (1 - z) ^ (k - S.card) * z ^ S.card * c S) = wordPoly k c := rfl
  rw [e] at hsum
  refine hsum.congr_deriv ?_
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul]
  congr 1
  · rw [Finset.sum_eq_single (∅ : Finset ℕ)]
    · simp
    · intro S _ hS
      rw [if_neg (fun h => hS (Finset.card_eq_zero.1 h))]
    · intro h
      exact absurd (Finset.empty_mem_powerset _) h
  · rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, Finset.powersetCard_one,
      Finset.sum_map]
    rfl

/-- **Cauchy estimate for word polynomials**: a bound on `ball 0 r` bounds the linear
coefficient. -/
theorem norm_linCoef_wordPoly_le (k : ℕ) (c : Finset ℕ → ℂ) {r B : ℝ} (hr : 0 < r)
    (hB : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖wordPoly k c z‖ ≤ B) :
    ‖-(k : ℂ) * c ∅ + ∑ i ∈ Finset.range k, c {i}‖ ≤ 2 * B / r := by
  have hd := (hasDerivAt_wordPoly_zero k c).deriv
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := r / 2)
    (C := B) (f := wordPoly k c) (by positivity)
    (differentiable_wordPoly k c).diffContOnCl fun z hz => hB z (by
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball, hz]
      linarith)
  rw [hd] at hC
  calc _ ≤ B / (r / 2) := hC
    _ = 2 * B / r := by field_simp

/-! ## The survival polynomials -/

/-- The coefficients of `cSurv`. -/
def survCoef (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) (S : Finset ℕ) : ℂ :=
  ((survInt eps (wordLaw ν σ S) k G : ℝ) : ℂ)

theorem cSurv_eq_wordPoly (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) :
    (fun z => cSurv eps ν σ z k G) = wordPoly k (survCoef eps ν σ k G) := rfl

theorem differentiable_cSurv (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) :
    Differentiable ℂ (fun z => cSurv eps ν σ z k G) := by
  rw [cSurv_eq_wordPoly]; exact differentiable_wordPoly _ _

theorem wordLaw_empty (ν σ : ProbabilityMeasure ℝ) : wordLaw ν σ ∅ = iidLaw ν :=
  piLaw_congr fun j => by simp

theorem cSurv_zero (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) :
    cSurv eps ν σ 0 k G = ((survInt eps (iidLaw ν) k G : ℝ) : ℂ) := by
  have e : cSurv eps ν σ 0 k G = wordPoly k (survCoef eps ν σ k G) 0 := rfl
  rw [e, wordPoly_zero, survCoef, wordLaw_empty]

/-- The linear coefficient of the survival polynomial. -/
def survLin (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) : ℝ :=
  -(k : ℝ) * survInt eps (iidLaw ν) k G +
    ∑ i ∈ Finset.range k, survInt eps (wordLaw ν σ {i}) k G

theorem hasDerivAt_cSurv_zero (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) :
    HasDerivAt (fun z => cSurv eps ν σ z k G) ((survLin eps ν σ k G : ℝ) : ℂ) 0 := by
  rw [cSurv_eq_wordPoly]
  refine (hasDerivAt_wordPoly_zero k (survCoef eps ν σ k G)).congr_deriv ?_
  simp only [survLin, survCoef, wordLaw_empty]
  push_cast
  rfl

/-- **Cauchy estimate** for the survival polynomial. -/
theorem abs_survLin_le (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (k : ℕ) (G : ℝ → ℝ) {r B : ℝ}
    (hr : 0 < r) (hB : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖cSurv eps ν σ z k G‖ ≤ B) :
    |survLin eps ν σ k G| ≤ 2 * B / r := by
  have h := norm_linCoef_wordPoly_le k (survCoef eps ν σ k G) hr hB
  have e : -(k : ℂ) * survCoef eps ν σ k G ∅ + ∑ i ∈ Finset.range k, survCoef eps ν σ k G {i} =
      ((survLin eps ν σ k G : ℝ) : ℂ) := by
    simp only [survLin, survCoef, wordLaw_empty]
    push_cast
    rfl
  rwa [e, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The survival polynomial on the real segment** is the survival integral under the mixture
product. -/
theorem cSurv_ofReal (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (k : ℕ) {G : ℝ → ℝ} (hG : Measurable G)
    (hint : ∀ S ∈ (Finset.range k).powerset,
      Integrable ((survSet eps k).indicator (fun g => G (gapKeys g k))) (wordLaw ν σ S)) :
    cSurv eps ν σ (t : ℂ) k G = ((survInt eps (iidLaw (mixPM ν σ t)) k G : ℝ) : ℂ) := by
  rw [survInt, integral_iidLaw_mix ν σ ht (measurable_survInd eps k hG)
    (depPrefix_survInd eps k G) hint, cSurv_eq]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [wordCoef, survInt]
  push_cast
  ring

/-! ## The occupation terms -/

/-- The occupation term `Ψ_k(z) = (1 - z) cSurv_k(G_ν) + z cSurv_k(G_σ)`. -/
def occTerm (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (Gν Gσ : ℝ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * cSurv eps ν σ z k Gν + z * cSurv eps ν σ z k Gσ

theorem differentiable_occTerm (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (Gν Gσ : ℝ → ℝ)
    (k : ℕ) : Differentiable ℂ (occTerm eps ν σ Gν Gσ k) := by
  have h1 := differentiable_cSurv eps ν σ k Gν
  have h2 := differentiable_cSurv eps ν σ k Gσ
  unfold occTerm
  fun_prop

/-- The derivative of the occupation term at `0`. -/
def occDeriv (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (Gν Gσ : ℝ → ℝ) (k : ℕ) : ℝ :=
  -survInt eps (iidLaw ν) k Gν + survLin eps ν σ k Gν + survInt eps (iidLaw ν) k Gσ

theorem hasDerivAt_occTerm_zero (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (Gν Gσ : ℝ → ℝ)
    (k : ℕ) : HasDerivAt (occTerm eps ν σ Gν Gσ k) ((occDeriv eps ν σ Gν Gσ k : ℝ) : ℂ) 0 := by
  have h1 := hasDerivAt_cSurv_zero eps ν σ k Gν
  have h2 := hasDerivAt_cSurv_zero eps ν σ k Gσ
  have hP := ((hasDerivAt_id (0 : ℂ)).const_sub 1).mul h1
  have hQ := (hasDerivAt_id (0 : ℂ)).mul h2
  have h := hP.add hQ
  refine h.congr_deriv ?_
  simp only [occDeriv, cSurv_zero, id]
  push_cast
  ring

theorem norm_occTerm_le (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (Gν Gσ : ℝ → ℝ) (k : ℕ)
    {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    ‖occTerm eps ν σ Gν Gσ k z‖ ≤
      (1 + r) * ‖cSurv eps ν σ z k Gν‖ + r * ‖cSurv eps ν σ z k Gσ‖ := by
  unfold occTerm
  calc ‖(1 - z) * cSurv eps ν σ z k Gν + z * cSurv eps ν σ z k Gσ‖
      ≤ ‖1 - z‖ * ‖cSurv eps ν σ z k Gν‖ + ‖z‖ * ‖cSurv eps ν σ z k Gσ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (1 + r) * ‖cSurv eps ν σ z k Gν‖ + r * ‖cSurv eps ν σ z k Gσ‖ := by
        have h1 : ‖1 - z‖ ≤ 1 + r := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
        gcongr

end

end PGM
