import PLAStochastic.ForMathlib.Analysis.Fourier.FiniteBand
import PLAStochastic.Index.CEPS.Inversion.Main

/-!
# Finite-order Fourier inversion assembly

The weighted Sobolev expansion of order `N` with derivative budget `m` needs only
finitely many orders of the three-band input: the low band and the coefficient
envelopes through `2 N + 2`, and the high band through
`fourierHighOrder δ (m + 1) (2 N + 2)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ContDiff

namespace PGM

/-- Uniform expansions through order `P` and a common actual envelope give finite
coefficient jet envelopes. -/
theorem finite_expansion_jet_envelopes_upTo {F : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ} {m P : ℕ}
    (hu : ∀ r ≤ m, UniformInverseExpansionUpTo (fun eps => iteratedDeriv r (F eps))
      (fun k => iteratedDeriv r (g k)) P)
    (henv : ∃ D θ : ℝ, 0 ≤ D ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ r ≤ m, ∀ x, |iteratedDeriv r (F eps) x| ≤ D * Real.exp (-θ * |x|)) :
    ∃ D θ : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ᶠ eps in atTop, ∀ r ≤ m, ∀ x, |iteratedDeriv r (F eps) x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ k ≤ P, ∀ r ≤ m, ∀ x, |iteratedDeriv r (g k) x| ≤ D * Real.exp (-θ * |x|) := by
  classical
  obtain ⟨D₀, θ₀, hD₀, hθ₀, he⟩ := henv
  obtain ⟨E₀, hE₀⟩ := eventually_atTop.mp he
  have hsingle (r : Fin (m + 1)) : ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ eps ≥ E, ∀ x, |iteratedDeriv r (F eps) x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ k ≤ P, ∀ x, |iteratedDeriv r (g k) x| ≤ D * Real.exp (-θ * |x|) :=
    (hu r (by omega)).finite_coefficient_envelopes
      ⟨D₀, θ₀, E₀, hD₀, hθ₀, fun eps he x => hE₀ eps he r (by omega) x⟩
  choose D θ E hD hθ hF hg using hsingle
  let S : Finset (Fin (m + 1)) := univ
  have hS : S.Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  let Θ := S.inf' hS θ
  let B := ∑ r ∈ S, D r
  let Emax := S.sup' hS E
  have hΘ : 0 < Θ := (Finset.lt_inf'_iff hS).mpr fun r _ => hθ r
  have hB : 0 ≤ B := sum_nonneg fun r _ => hD r
  have hbound (r : Fin (m + 1)) (x : ℝ) :
      D r * Real.exp (-θ r * |x|) ≤ B * Real.exp (-Θ * |x|) := by
    have hrD : D r ≤ B := single_le_sum (fun j _ => hD j) (mem_univ r)
    have hrΘ : Θ ≤ θ r := Finset.inf'_le θ (mem_univ r)
    exact mul_le_mul hrD (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x]))
      (Real.exp_pos _).le hB
  refine ⟨B, Θ, hB, hΘ, eventually_atTop.mpr ⟨Emax, ?_⟩, ?_⟩
  · intro eps he r hr x
    let j : Fin (m + 1) := ⟨r, by omega⟩
    exact (hF j eps ((Finset.le_sup' E (mem_univ j)).trans he) x).trans (hbound j x)
  · intro k hk r hr x
    let j : Fin (m + 1) := ⟨r, by omega⟩
    exact (hg j k hk x).trans (hbound j x)

/-- Finite real-space assembly: uniform derivative expansions through order `2 N + 1`
for derivatives through `m`, bounded actual derivatives through `m + 1` and the
density envelope give the weighted Sobolev remainder of order `N + 1`. -/
theorem cepsSobolev_expansion_of_uniform_upTo {F : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ} {m N : ℕ}
    (hf : ∀ᶠ eps in atTop, ContDiff ℝ (m + 1) (F eps))
    (hg : ∀ k ≤ 2 * N + 1, ContDiff ℝ m (g k))
    (hu : ∀ r ≤ m, UniformInverseExpansionUpTo (fun eps => iteratedDeriv r (F eps))
      (fun k => iteratedDeriv r (g k)) (2 * N + 1))
    (hbounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop,
      ∀ r ≤ m + 1, ∀ x, |iteratedDeriv r (F eps) x| ≤ B)
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) :
    ∃ η : ℝ, 0 < η ∧ (∀ k ≤ N, CepsSobolevClass m η (g k)) ∧
      (∀ᶠ eps in atTop, CepsSobolevClass m η (F eps)) ∧
      IsInverseOrder (fun eps => cepsSobolev m η (cepsInversionRemainder F g N eps)) (N + 1) := by
  classical
  set M := 2 * N + 1 with hMdef
  obtain ⟨A, θ₀, hA, hθ₀, ha⟩ := henv
  obtain ⟨B₀, hB₀, hb₀⟩ := hbounded
  obtain ⟨D₀, ρ, hD₀, hρ, he⟩ := eventually_finite_exponential_jets hA hB₀ hθ₀ hf hb₀ ha
  obtain ⟨D, θ, hD, hθ, hFenv, hgenv⟩ := finite_expansion_jet_envelopes_upTo hu ⟨D₀, ρ, hD₀, hρ, he⟩
  have hfm : ∀ᶠ eps in atTop, ContDiff ℝ m (F eps) :=
    hf.mono fun _ h => h.of_le (by exact_mod_cast Nat.le_succ m)
  have hgM (k : ℕ) (hk : k ∈ range (M + 1)) : ContDiff ℝ m (g k) :=
    hg k (by have := mem_range.mp hk; omega)
  let η := θ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηθ : η < θ := by dsimp [η]; linarith
  have hηhalf : η < θ / 2 := by dsimp [η]; linarith
  have hgclass (k : ℕ) (hk : k ≤ M) : CepsSobolevClass m η (g k) :=
    ⟨hg k hk, fun r hr => (weighted_integrable_of_envelope
      ((hg k hk).continuous_iteratedDeriv r (by exact_mod_cast hr)).aestronglyMeasurable hD hηθ
      (hgenv k hk r hr)).1⟩
  have hFclass : ∀ᶠ eps in atTop, CepsSobolevClass m η (F eps) := by
    filter_upwards [hfm, hFenv] with eps hcd henv
    exact ⟨hcd, fun r hr => (weighted_integrable_of_envelope
      (hcd.continuous_iteratedDeriv r (by exact_mod_cast hr)).aestronglyMeasurable hD hηθ
        (henv r hr)).1⟩
  have hderiv {eps : ℝ} (hcd : ContDiff ℝ m (F eps)) (P r : ℕ) (hP : P ≤ M) (hr : r ≤ m)
      (x : ℝ) :
      iteratedDeriv r (cepsInversionRemainder F g P eps) x =
        iteratedDeriv r (F eps) x - ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x :=
    iteratedDeriv_inverseRemainder (hcd.of_le (by exact_mod_cast hr)) _
      (fun k hk => (hg k (by have := mem_range.mp hk; omega)).of_le (by exact_mod_cast hr)) _ x
  have hremenv : ∀ᶠ eps in atTop, ∀ r ≤ m, ∀ x,
      |iteratedDeriv r (cepsInversionRemainder F g M eps) x| ≤
        ((M : ℝ) + 2) * D * Real.exp (-θ * |x|) := by
    filter_upwards [hfm, hFenv, eventually_ge_atTop (1 : ℝ)] with eps hcd henv heps r hr x
    rw [hderiv hcd M r le_rfl hr x]
    have hi0 : 0 ≤ eps⁻¹ := by positivity
    have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < eps)).mpr heps
    have hsum : |∑ k ∈ range (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x| ≤
        ((M : ℝ) + 1) * D * Real.exp (-θ * |x|) := by
      calc
        _ ≤ ∑ k ∈ range (M + 1), |(eps⁻¹) ^ k * iteratedDeriv r (g k) x| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ range (M + 1), D * Real.exp (-θ * |x|) := by
          apply sum_le_sum
          intro k hk
          rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 _)]
          exact (mul_le_mul (pow_le_one₀ hi0 hi1)
            (hgenv k (by have := mem_range.mp hk; omega) r hr x)
            (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
        _ = _ := by simp; ring
    exact (abs_sub _ _).trans ((add_le_add (henv r hr x) hsum).trans_eq (by ring))
  have hremOrder (r : ℕ) (hr : r ≤ m) :
      IsInverseOrder (fun eps => ∫ x, Real.exp (η * |x|) *
        |iteratedDeriv r (cepsInversionRemainder F g M eps) x|) (N + 1) := by
    apply weighted_inverseOrder_of_uniform hηhalf
    · obtain ⟨K, E, hK⟩ := hu r hr M le_rfl
      obtain ⟨E', hE'⟩ := eventually_atTop.mp hfm
      refine ⟨K, max E E', fun eps he x => ?_⟩
      rw [hderiv (hE' eps ((le_max_right _ _).trans he)) M r le_rfl hr x]
      have hh := hK eps ((le_max_left _ _).trans he) x
      have hpoly : inversePolynomial (fun k => iteratedDeriv r (g k) x) M eps =
          ∑ k ∈ range (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x := by
        unfold inversePolynomial
        exact sum_congr rfl fun _ _ => mul_comm _ _
      rw [hpoly] at hh
      have hp : M + 1 = 2 * (N + 1) := by omega
      simpa only [hp] using hh
    · obtain ⟨E, hE⟩ := eventually_atTop.mp (hfm.and hremenv)
      refine ⟨((M : ℝ) + 2) * D, E, fun eps he => ⟨?_, (hE eps he).2 r hr⟩⟩
      have hc : ContDiff ℝ m (cepsInversionRemainder F g M eps) :=
        (hE eps he).1.sub (ContDiff.sum fun k hk => contDiff_const.mul (hgM k hk))
      exact (hc.continuous_iteratedDeriv r (by exact_mod_cast hr)).aestronglyMeasurable
  have horders (r : Fin (m + 1)) := (hremOrder r (by omega)).nonneg_witness
  choose K E _hK _hE hKe using horders
  let Emax := univ.sup'
    (show (univ : Finset (Fin (m + 1))).Nonempty from ⟨⟨0, by omega⟩, mem_univ _⟩) E
  let J := ∫ x : ℝ, Real.exp (-(θ - η) * |x|)
  have hJE : Integrable (fun x : ℝ => Real.exp (-(θ - η) * |x|)) :=
    integrable_exp_neg_abs (by linarith)
  let T := ((M : ℝ) + 1) * D
  obtain ⟨Ef, hEf⟩ := eventually_atTop.mp (hfm.and hFenv)
  refine ⟨η, hη, fun k hk => hgclass k (by omega), hFclass,
    ∑ r : Fin (m + 1), K r + (m + 1 : ℕ) * T * J, max 1 (max Emax Ef), fun eps heps => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have heE : Emax ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans heps)
  have hef : Ef ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans heps)
  obtain ⟨hcd, henv⟩ := hEf eps hef
  have hi0 : 0 ≤ eps⁻¹ := by positivity
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < eps)).mpr he1
  have hNM : N ≤ M := by omega
  have hpoint (r : ℕ) (hr : r ≤ m) (x : ℝ) :
      |iteratedDeriv r (cepsInversionRemainder F g N eps) x| ≤
        |iteratedDeriv r (cepsInversionRemainder F g M eps) x| +
          T * (eps⁻¹) ^ (N + 1) * Real.exp (-θ * |x|) := by
    rw [hderiv hcd N r hNM hr x, hderiv hcd M r le_rfl hr x]
    have hsplit := sum_range_add_sum_Ico (fun k => (eps⁻¹) ^ k * iteratedDeriv r (g k) x)
      (show N + 1 ≤ M + 1 by omega)
    have htail : |∑ k ∈ Ico (N + 1) (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x| ≤
        T * (eps⁻¹) ^ (N + 1) * Real.exp (-θ * |x|) := by
      calc
        _ ≤ ∑ k ∈ Ico (N + 1) (M + 1), |(eps⁻¹) ^ k * iteratedDeriv r (g k) x| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Ico (N + 1) (M + 1), (eps⁻¹) ^ (N + 1) * D * Real.exp (-θ * |x|) := by
          apply sum_le_sum
          intro k hk
          rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 _)]
          exact (mul_le_mul (pow_le_pow_of_le_one hi0 hi1 (mem_Ico.mp hk).1)
            (hgenv k (by have := (mem_Ico.mp hk).2; omega) r hr x) (abs_nonneg _)
            (by positivity)).trans_eq (by ring)
        _ ≤ _ := by
          simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
          dsimp [T]
          have hcard : ((M + 1 - (N + 1) : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
            exact_mod_cast Nat.sub_le (M + 1) (N + 1)
          exact (mul_le_mul_of_nonneg_right hcard
            (by positivity : 0 ≤ (eps⁻¹) ^ (N + 1) * D * Real.exp (-θ * |x|))).trans_eq
            (by ring)
    have heq : iteratedDeriv r (F eps) x -
        ∑ k ∈ range (N + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x =
        (iteratedDeriv r (F eps) x -
          ∑ k ∈ range (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x) +
          ∑ k ∈ Ico (N + 1) (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x := by
      rw [← hsplit]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add le_rfl htail)
  have hInt (r : Fin (m + 1)) :
      (∫ x, Real.exp (η * |x|) * |iteratedDeriv r (cepsInversionRemainder F g N eps) x|) ≤
        (K r + T * J) * (eps⁻¹) ^ (N + 1) := by
    have hr : (r : ℕ) ≤ m := by omega
    have hRhi : Integrable (fun x => Real.exp (η * |x|) *
        |iteratedDeriv r (cepsInversionRemainder F g M eps) x|) := by
      have hc : ContDiff ℝ m (cepsInversionRemainder F g M eps) := hcd.sub
        (ContDiff.sum fun k hk => contDiff_const.mul (hgM k hk))
      have hen : ∀ x, |iteratedDeriv r (cepsInversionRemainder F g M eps) x| ≤
          ((M : ℝ) + 2) * D * Real.exp (-θ * |x|) := by
        intro x
        rw [hderiv hcd M r le_rfl hr x]
        have hfenv := henv r hr x
        have hsum : |∑ k ∈ range (M + 1), (eps⁻¹) ^ k * iteratedDeriv r (g k) x| ≤
            ∑ _k ∈ range (M + 1), D * Real.exp (-θ * |x|) := by
          apply (abs_sum_le_sum_abs _ _).trans
          apply sum_le_sum
          intro k hk
          rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 _)]
          exact (mul_le_mul (pow_le_one₀ hi0 hi1)
            (hgenv k (by have := mem_range.mp hk; omega) r hr x)
            (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
        simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
        exact (abs_sub _ _).trans ((add_le_add hfenv hsum).trans_eq (by ring))
      have hi := (weighted_integrable_of_envelope
        (hc.continuous_iteratedDeriv r (by exact_mod_cast hr)).aestronglyMeasurable
        (by positivity) hηθ hen).1
      simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi.abs
    have hmajor : Integrable (fun x => Real.exp (η * |x|) *
        |iteratedDeriv r (cepsInversionRemainder F g M eps) x| +
          (T * (eps⁻¹) ^ (N + 1)) * Real.exp (-(θ - η) * |x|)) :=
      hRhi.add (hJE.const_mul _)
    have hbpoint (x : ℝ) : Real.exp (η * |x|) *
        |iteratedDeriv r (cepsInversionRemainder F g N eps) x| ≤
      Real.exp (η * |x|) * |iteratedDeriv r (cepsInversionRemainder F g M eps) x| +
        (T * (eps⁻¹) ^ (N + 1)) * Real.exp (-(θ - η) * |x|) := by
      have hh := mul_le_mul_of_nonneg_left (hpoint r hr x) (Real.exp_pos (η * |x|)).le
      rw [mul_add] at hh
      have hex : Real.exp (η * |x|) * Real.exp (-θ * |x|) =
          Real.exp (-(θ - η) * |x|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      exact hh.trans_eq (by rw [← hex]; ring)
    have hcN : ContDiff ℝ m (cepsInversionRemainder F g N eps) := hcd.sub
      (ContDiff.sum fun k hk => contDiff_const.mul
        (hg k (by have := mem_range.mp hk; omega)))
    have hcn := hcN.continuous_iteratedDeriv r (by exact_mod_cast hr)
    have hNhi : Integrable (fun x => Real.exp (η * |x|) *
        |iteratedDeriv r (cepsInversionRemainder F g N eps) x|) :=
      hmajor.mono' ((by fun_prop : Continuous fun x : ℝ => Real.exp (η * |x|)).aestronglyMeasurable.mul
          hcn.abs.aestronglyMeasurable)
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbpoint x)
    have hbInt := integral_mono hNhi hmajor hbpoint
    rw [integral_add hRhi (hJE.const_mul _), integral_const_mul] at hbInt
    have hh := hKe r eps ((Finset.le_sup' E (mem_univ r)).trans heE)
    rw [abs_of_nonneg (integral_nonneg fun _ => by positivity)] at hh
    calc
      _ ≤ _ := hbInt
      _ ≤ K r * (eps⁻¹) ^ (N + 1) +
          (T * (eps⁻¹) ^ (N + 1)) * ∫ x : ℝ, Real.exp (-(θ - η) * |x|) :=
        add_le_add hh le_rfl
      _ = _ := by dsimp [J]; ring
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _), cepsSobolev]
  rw [← Fin.sum_univ_eq_sum_range]
  apply (sum_le_sum fun r _ => hInt r).trans_eq
  rw [← sum_mul, sum_add_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Finite-order density form of the inversion assembly: the weighted Sobolev expansion of
order `N` with derivative budget `m` uses the low band through `2 N + 2` and the high band
through `fourierHighOrder δ (m + 1) (2 N + 2)`. -/
theorem cepsFourier_sobolev_expansion_of_density_upTo {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R) (m N : ℕ)
    (hQ : 2 * N + 2 ≤ Q) (hR : fourierHighOrder δ (m + 1) (2 * N + 2) ≤ R)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) :
    ∃ η : ℝ, 0 < η ∧ (∀ k ≤ N, CepsSobolevClass m η (angularRealInverse (a k))) ∧
      (∀ᶠ eps in atTop, CepsSobolevClass m η (F eps)) ∧
      IsInverseOrder (fun eps => cepsSobolev m η
        (cepsInversionRemainder F (fun k => angularRealInverse (a k)) N eps)) (N + 1) := by
  have hδ := h.delta_pos
  have hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps) := by
    filter_upwards [hF] with eps he
    rw [he.2.2]
    exact (continuous_charIntegral he.1).aestronglyMeasurable
  have ha := h.coefficient_aestronglyMeasurable hφ
  have hR0 : fourierHighOrder δ 0 0 ≤ R :=
    (fourierHighOrder_mono (Nat.zero_le _) (Nat.zero_le _) hδ).trans hR
  have hR1 : fourierHighOrder δ (m + 1) 0 ≤ R :=
    (fourierHighOrder_mono le_rfl (Nat.zero_le _) hδ).trans hR
  have heq := h.eventually_inverse_eq_density hR0 hφ hF
  obtain ⟨B, hB, hb⟩ := h.actual_inverse_bounded hφ (m + 1) hR1
  have hcd : ∀ᶠ eps in atTop, ContDiff ℝ (m + 1) (F eps) := by
    filter_upwards [hb, heq] with eps he hre
    rw [hre] at he
    exact he.1
  have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop,
      ∀ r ≤ m + 1, ∀ x, |iteratedDeriv r (F eps) x| ≤ B := by
    refine ⟨B, hB, ?_⟩
    filter_upwards [hb, heq] with eps he hre
    rw [hre] at he
    exact he.2
  have hu : ∀ r ≤ m, UniformInverseExpansionUpTo (fun eps => iteratedDeriv r (F eps))
      (fun k => iteratedDeriv r (angularRealInverse (a k))) (2 * N + 1) := fun r hr =>
    (h.uniform_inverse_expansion hφ ha r (2 * N + 1) (by omega)
      ((fourierHighOrder_mono (by omega) le_rfl hδ).trans hR)).congr_eventually
      (heq.mono fun eps he => congrArg (iteratedDeriv r) he)
  exact cepsSobolev_expansion_of_uniform_upTo hcd
    (fun k hk => h.coefficient_contDiff ha m k (by omega)) hu hbound henv

/-- The coefficient densities through order `Q` are smooth. -/
theorem cepsFourier_coefficient_contDiff_upTo {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ)) :
    ∀ k ≤ Q, ContDiff ℝ ∞ (angularRealInverse (a k)) := by
  have hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps) := by
    filter_upwards [hF] with eps he
    rw [he.2.2]
    exact (continuous_charIntegral he.1).aestronglyMeasurable
  intro k hk
  exact contDiff_infty.mpr fun n =>
    h.coefficient_contDiff (h.coefficient_aestronglyMeasurable hφ) n k hk

end PGM
