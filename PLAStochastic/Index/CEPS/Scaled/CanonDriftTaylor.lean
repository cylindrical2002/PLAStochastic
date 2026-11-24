import PLAStochastic.Index.CEPS.Canonical.MixedBounds
import PLAStochastic.Index.CEPS.Normal.ActualBudget
import PLAStochastic.ForMathlib.Analysis.Calculus.TaylorSegment

/-! # Genuine drift Taylor surrogates of the canonical factor

The drift is real in the original factor. Its finite Taylor polynomial extends
holomorphically to complex drift; no complex-drift holomorphy of the original
factor is asserted. The approximation bound is uniform in discount and mark.
-/

noncomputable section
open Complex Set Metric MeasureTheory Finset Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}

/-- The actual real-drift jet at zero, keeping both holomorphic parameters. -/
def cepsCanonDriftCoeff (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (j : ℕ) (q ζ : ℂ) : ℂ :=
  iteratedDeriv j (fun μ : ℝ => dom.canonL ρW μ q ζ) 0

/-- Degree-`N` drift surrogate, evaluated at a possibly complex drift. -/
def cepsCanonDriftTaylor (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (N : ℕ) (μ q ζ : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * μ ^ j * cepsCanonDriftCoeff dom ρW j q ζ

namespace CepsCanonDomain

def canonDriftCoeffBound (dom : CepsCanonDomain D θ v) (j : ℕ) (M : ℝ) : ℝ :=
  match j with
  | 0 => dom.normalLogBound
  | n + 1 => 3 * (dom.jetC n * (M + 1)) / (2 * dom.c₀)

def canonDriftTaylorBound (dom : CepsCanonDomain D θ v) (N : ℕ) (M r : ℝ) : ℝ :=
  ∑ j ∈ range (N + 1), (j.factorial : ℝ)⁻¹ * r ^ j * dom.canonDriftCoeffBound j M

end CepsCanonDomain

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonDriftCoeff_succ {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {j : ℕ} (hj : j + 2 ≤ m) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    cepsCanonDriftCoeff dom ρW (j + 1) q ζ = cepsCanonLJet D θ ρW dom.c₀ j 0 q ζ := by
  exact dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hq hζ j hj 0
    (by have := dom.μ₀_pos; simp; positivity)

include hW hθ hD in
theorem cepsCanonDriftCoeff_differentiableOn {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (j : ℕ) (hj : j + 1 ≤ m) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftCoeff dom ρW j x.2 x.1)
      {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀ / 2} := by
  cases j with
  | zero =>
    have h := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) (μ := 0)
      (by simp; exact dom.μ₀_pos.le) (by simp)
    exact h.mono fun x hx => ⟨hx.1, by have hxq := hx.2; linarith [dom.q₀_pos]⟩
  | succ j =>
    have h := dom.differentiableOn_cepsCanonLJet hW hθ hD hf hη (n := j) (by omega)
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) (t := 0)
      (by have := dom.μ₀_pos; simp; positivity)
    exact h.congr fun x hx => (cepsCanonDriftCoeff_succ dom hW hθ hD hf hη (by omega)
      hx.2.le hx.1)

include hW hθ hD in
theorem cepsCanonDriftCoeff_norm_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (j : ℕ) (hj : j + 1 ≤ m)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖cepsCanonDriftCoeff dom ρW j q ζ‖ ≤ dom.canonDriftCoeffBound j M := by
  cases j with
  | zero =>
    exact dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) (μ := 0)
      (by simp; exact dom.μ₀_pos.le) (by simp) (hq.trans (by linarith [dom.q₀_pos])) hζ
  | succ j =>
    have hzr : ζ.re < dom.c₀ := by linarith [re_le_norm ζ, dom.c₀_pos]
    rw [cepsCanonDriftCoeff_succ dom hW hθ hD hf hη (by omega) hq hzr]
    have h := dom.norm_cepsCanonLJet_le_uniform hW hθ hD hf hη (n := j) (by omega)
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) (t := 0)
      (by simp; exact div_nonneg dom.μ₀_pos.le (by norm_num)) hq
      ((re_le_norm ζ).trans hζ)
    apply h.trans
    change _ ≤ 3 * (dom.jetC j * (M + 1)) / (2 * dom.c₀)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (show cepsSobolev m η fW + 1 ≤ M + 1 by linarith) (dom.jetC_nonneg hD j))
        (by norm_num)) (by have := dom.c₀_pos; positivity)

include hW hθ hD in
theorem hasDerivAt_cepsCanonL_iteratedDrift {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (j : ℕ) (hj : j + 2 ≤ m) {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    HasDerivAt (iteratedDeriv j (fun t : ℝ => dom.canonL ρW t q ζ))
      (iteratedDeriv (j + 1) (fun t : ℝ => dom.canonL ρW t q ζ) μ) μ := by
  cases j with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_add, iteratedDeriv_one]
    exact (dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf (by omega) hη
      (γ := 1) (by norm_num) le_rfl (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos])
      (by linarith [dom.μ₀_pos]) hq hζ).differentiableAt.hasDerivAt
  | succ j =>
    have hopen : IsOpen {t : ℝ | |t| < dom.μ₀ / 4} :=
      isOpen_lt continuous_abs continuous_const
    have hev : iteratedDeriv (j + 1) (fun t : ℝ => dom.canonL ρW t q ζ) =ᶠ[𝓝 μ]
        fun t => cepsCanonLJet D θ ρW dom.c₀ j t q ζ :=
      eventually_of_mem (hopen.mem_nhds hμ) fun t ht =>
        dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη (γ := 1) (by norm_num) le_rfl
          (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hq hζ j (by omega) t ht
    have hd := dom.hasDerivAt_cepsCanonLJet hW hθ hD hf hη (n := j) (by omega)
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ hq hζ
    have hi := dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hq hζ (j + 1) (by omega) μ hμ
    exact (hd.congr_of_eventuallyEq hev).congr_deriv hi.symm

theorem cepsCanonDriftTaylor_zero (N : ℕ) (q ζ : ℂ) :
    cepsCanonDriftTaylor dom ρW N 0 q ζ = dom.canonL ρW 0 q ζ := by
  unfold cepsCanonDriftTaylor
  rw [sum_range_succ']
  simp [cepsCanonDriftCoeff]

include hW hθ hD in
theorem cepsCanonDriftTaylor_differentiableOn {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m) :
    DifferentiableOn ℂ
      (fun x : ℂ × (ℂ × ℂ) => cepsCanonDriftTaylor dom ρW N x.1 x.2.1 x.2.2)
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
  have hopen : IsOpen {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < dom.q₀ / 2} :=
    (isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_snd.norm) continuous_const)
  have hdterm : ∀ j ∈ range (N + 1), ∀ x : ℂ × (ℂ × ℂ),
      x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2 →
      DifferentiableAt ℂ (fun x : ℂ × (ℂ × ℂ) =>
        (j.factorial : ℂ)⁻¹ * x.1 ^ j * cepsCanonDriftCoeff dom ρW j x.2.1 x.2.2) x := by
    intro j hj x hx
    have hcoeff := cepsCanonDriftCoeff_differentiableOn dom hW hθ hD hf hη j
      (by have := mem_range.mp hj; omega)
    have hg : DifferentiableAt ℂ (fun x : ℂ × (ℂ × ℂ) => (x.2.2, x.2.1)) x := by fun_prop
    have hc : DifferentiableAt ℂ
        (fun x : ℂ × (ℂ × ℂ) => cepsCanonDriftCoeff dom ρW j x.2.1 x.2.2) x := by
      simpa only [Function.comp_apply] using!
        (((hcoeff _ hx).differentiableAt (hopen.mem_nhds hx)).comp x hg)
    have hm : DifferentiableAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.1) x := by fun_prop
    exact ((hm.pow j).const_mul _).mul hc
  intro x hx
  exact (DifferentiableAt.fun_sum (fun j hj => hdterm j hj x hx)).differentiableWithinAt

include hW hθ hD in
theorem cepsCanonDriftTaylor_norm_le {m : ℕ} {η M r : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ r) (hq : ‖q‖ ≤ dom.q₀ / 2)
    (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖cepsCanonDriftTaylor dom ρW N μ q ζ‖ ≤ dom.canonDriftTaylorBound N M r := by
  unfold cepsCanonDriftTaylor CepsCanonDomain.canonDriftTaylorBound
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (norm_nonneg _) hμ j
    · positivity
  · exact cepsCanonDriftCoeff_norm_le dom hW hθ hD hf hη hM j
      (by have := mem_range.mp hj; omega) hq hζ
  · exact norm_nonneg _
  · have hr : 0 ≤ r := (norm_nonneg μ).trans hμ
    positivity

theorem cepsCanonDriftTaylor_real_eq (N : ℕ) (μ : ℝ) (q ζ : ℂ) :
    cepsCanonDriftTaylor dom ρW N μ q ζ =
      realTaylorSum (fun t : ℝ => dom.canonL ρW t q ζ) (N + 1) 0 μ := by
  unfold cepsCanonDriftTaylor realTaylorSum cepsCanonDriftCoeff
  apply sum_congr rfl
  intro j _
  rw [Complex.real_smul]
  push_cast
  simp

include hW hθ hD in
theorem cepsCanonDriftTaylor_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖dom.canonL ρW μ q ζ - cepsCanonDriftTaylor dom ρW N μ q ζ‖ ≤
      dom.canonDriftCoeffBound (N + 1) M * |μ| ^ (N + 1) := by
  have hzr : ζ.re < dom.c₀ := by linarith [re_le_norm ζ, dom.c₀_pos]
  have hseg : ∀ t ∈ uIcc 0 μ, |t| < dom.μ₀ / 4 := by
    intro t ht
    have h := abs_sub_left_of_mem_uIcc ht
    simp only [sub_zero] at h
    exact h.trans_lt hμ
  rw [cepsCanonDriftTaylor_real_eq dom]
  simpa only [sub_zero] using norm_sub_realTaylorSum_le (N + 1)
    (fun j hj t ht => hasDerivAt_cepsCanonL_iteratedDrift dom hW hθ hD hf hη j
      (by omega) (hseg t ht) hq hzr)
    (fun t ht => by
      change ‖iteratedDeriv (N + 1) (fun t : ℝ => cepsCanonL D θ ρW 1 dom.c₀ t q ζ) t‖ ≤ _
      rw [dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη (γ := 1) (by norm_num) le_rfl
        (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hq hzr N hN t (hseg t ht)]
      apply (dom.norm_cepsCanonLJet_le_uniform hW hθ hD hf hη hN
        (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) (hseg t ht).le hq
        ((re_le_norm ζ).trans hζ)).trans
      change _ ≤ 3 * (dom.jetC N * (M + 1)) / (2 * dom.c₀)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (show cepsSobolev m η fW + 1 ≤ M + 1 by linarith) (dom.jetC_nonneg hD N))
          (by norm_num)) (by have := dom.c₀_pos; positivity))

end PGM
