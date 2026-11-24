import PLAStochastic.Index.CEPS.Scaled.RootDirections
import PLAStochastic.Index.CEPS.Ident.CorollariesQ

/-! # The actual zero-discount root on each nonzero-drift half-line -/

noncomputable section
open Complex Set MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsRootR_zeroDiscount_ne_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hne : μ ≠ 0) :
    cepsRootR D θ ρW μ 0 ≠ 0 := by
  have hr := cepsRootR_norm_ge_drift dom hW hθ hD hμ (q := 0) (by simp)
  have hp : 0 < Real.sqrt (cepsVarLo D) / (3 * v) * |μ| := by
    have := CepsCanonDomain.v_pos hW hθ hD
    have := Real.sqrt_pos.mpr (cepsVarLo_pos hD)
    exact mul_pos (by positivity) (abs_pos.mpr hne)
  exact norm_pos_iff.mp (hp.trans_le hr)

include hW hθ hD in
theorem cepsRoots_zeroDiscount_one_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    cepsRootPlus D θ ρW μ 0 = 0 ∨ cepsRootMinus D θ ρW μ 0 = 0 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hz : cepsD ρW μ 0 0 = 0 := by
    rw [cepsD, stepTransform_zero hW]
    simp
  have hr := (dom.cepsD_eq_zero_iff hW hθ hD hμ'
    (ζ := 0) (q := 0) (by simp; exact dom.η_pos.le)
    (by simp; exact dom.q₀_pos.le) (by simp; linarith [dom.c₀_pos])).mp hz
  exact hr.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

include hW hθ hD in
theorem cepsRoots_zeroDiscount_of_pos {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    cepsRootPlus D θ ρW μ 0 = 0 ∧ (cepsRootMinus D θ ρW μ 0).re < 0 := by
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne'
  have hb := cepsRootMinus_re_ge_scale dom hW hθ hD hμ hp.le
    (q := 0) (by simp; exact dom.q₀_pos.le) (by simp)
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hbm : (cepsRootMinus D θ ρW μ 0).re < 0 := by
    have hscale : 0 < ‖cepsRootR D θ ρW μ 0‖ / (4 * Real.sqrt v) :=
      div_pos (norm_pos_iff.mpr hr) (by positivity)
    linarith
  refine ⟨?_, hbm⟩
  rcases cepsRoots_zeroDiscount_one_zero dom hW hθ hD hμ with h | h
  · exact h
  · rw [h, zero_re] at hbm
    exact False.elim (lt_irrefl _ hbm)

include hW hθ hD in
theorem cepsRoots_zeroDiscount_of_neg {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : μ < 0) :
    cepsRootMinus D θ ρW μ 0 = 0 ∧ 0 < (cepsRootPlus D θ ρW μ 0).re := by
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne
  have hb := cepsRootPlus_re_ge_scale dom hW hθ hD hμ hp.le
    (q := 0) (by simp; exact dom.q₀_pos.le) (by simp)
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hbp : 0 < (cepsRootPlus D θ ρW μ 0).re := by
    have hscale : 0 < ‖cepsRootR D θ ρW μ 0‖ / (4 * Real.sqrt v) :=
      div_pos (norm_pos_iff.mpr hr) (by positivity)
    linarith
  refine ⟨?_, hbp⟩
  rcases cepsRoots_zeroDiscount_one_zero dom hW hθ hD hμ with h | h
  · rw [h, zero_re] at hbp
    exact False.elim (lt_irrefl _ hbp)
  · exact h

end PGM
