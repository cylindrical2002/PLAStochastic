import PLAStochastic.Index.GEP.Kernel.BV.LongKernel

/-!
# The conventional long-kernel BV scale

This module converts the exact finite-time window estimate to `sqrt(w / n)`
variation and an exponentially small `n^(-1/2)` remainder. All constants depend
only on the original regular-law class.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem kBV_window_factor_le {c γ w H : ℝ} (hc : 0 < c) (hγ : 0 ≤ γ)
    (hw : 0 < w) (hH : 0 ≤ H) (n : ℕ) (hn : 8 ≤ n) :
    Real.sqrt (Real.exp (-(γ * (n / 4 : ℕ) / w ^ 2)) * H / (c * (n / 4 : ℕ))) ≤
      Real.sqrt (8 / c) / Real.sqrt (n : ℝ) *
        Real.exp (-(γ / 16 * n / w ^ 2)) * Real.sqrt H := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < (n / 4 : ℕ) := by exact_mod_cast (by omega : 0 < n / 4)
  have hm : (n : ℝ) ≤ 8 * (n / 4 : ℕ) := by exact_mod_cast (by omega : n ≤ 8 * (n / 4))
  have ht : γ * n / (8 * w ^ 2) ≤ γ * (n / 4 : ℕ) / w ^ 2 := by
    calc γ * n / (8 * w ^ 2) = γ * ((n : ℝ) / 8) / w ^ 2 := by ring
         _ ≤ γ * (n / 4 : ℕ) / w ^ 2 :=
           div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hγ) (sq_pos_of_pos hw).le
  have he := Real.exp_le_exp.mpr (neg_le_neg ht)
  have hd : 1 / (c * (n / 4 : ℕ)) ≤ (8 / c) / (n : ℝ) := by
    calc 1 / (c * (n / 4 : ℕ)) ≤ 8 / (c * n) := by
           apply (div_le_div_iff₀ (mul_pos hc hm0) (mul_pos hc hn0)).mpr
           have hmul := mul_le_mul_of_nonneg_left hm hc.le
           nlinarith
         _ = (8 / c) / (n : ℝ) := by ring
  have hprod : Real.exp (-(γ * (n / 4 : ℕ) / w ^ 2)) * H / (c * (n / 4 : ℕ)) ≤
      Real.exp (-(γ * n / (8 * w ^ 2))) * H * ((8 / c) / (n : ℝ)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul_of_nonneg_right he hH) hd
      (by positivity) (mul_nonneg (Real.exp_pos _).le hH)
  refine (Real.sqrt_le_sqrt hprod).trans_eq ?_
  rw [Real.sqrt_mul (mul_nonneg (Real.exp_pos _).le hH),
    Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_div (by positivity : 0 ≤ 8 / c),
    ← Real.exp_half]
  rw [show -(γ * (n : ℝ) / (8 * w ^ 2)) / 2 = -(γ / 16 * n / w ^ 2) by ring]
  ring

/-- Class-uniform constants for the actual long-kernel decomposition. -/
def kBVClassRho (D vlo vhi : ℝ) : ℝ := Real.sqrt (1 - killCnu D vlo vhi)
def kBVClassRate (D vlo vhi : ℝ) : ℝ := killGapConst (killCnu D vlo vhi) (1 / 2) / 16
def kBVClassRemConst (D vlo vhi : ℝ) : ℝ := Real.sqrt (8 / killCnu D vlo vhi)
def kBVClassVarConst (D vlo vhi : ℝ) : ℝ :=
  8 * Real.pi * (1 + 1 / (1 - kBVClassRho D vlo vhi)) * kBVClassRemConst D vlo vhi

theorem kBVClass_constants {D vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    0 ≤ kBVClassRho D vlo vhi ∧ kBVClassRho D vlo vhi < 1 ∧
      0 < kBVClassRate D vlo vhi ∧ 0 < kBVClassRemConst D vlo vhi ∧
      0 < kBVClassVarConst D vlo vhi := by
  have hc := killCnu_pos hD hvlo hvhi
  have hρ1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo hvhi
  have hgap := killGapConst_pos hc (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨Real.sqrt_nonneg _, hρ1, ?_, ?_, ?_⟩
  · exact div_pos hgap (by norm_num)
  · exact Real.sqrt_pos.mpr (div_pos (by norm_num) hc)
  · unfold kBVClassVarConst kBVClassRho kBVClassRemConst
    have hp : 0 < 1 - Real.sqrt (1 - killCnu D vlo vhi) := by linarith
    positivity

/-- The original long-kernel BV conclusion, with actual representatives and
explicit class-uniform constants. It applies to both signs of the residual
slope and never assumes BV regularity of the full killed kernel. -/
theorem kBV_regLaw_scaled_decomposition {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a α w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    {u : ℝ → ℂ} (hu : Measurable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) (n : ℕ) (hn : 8 ≤ n) :
    ∃ G R : KernelL2,
      ((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n)
        (h2.toLp u) = G + R ∧
      kBVHasRep (Icc α (α + w))
        (kBVClassVarConst D vlo vhi * Real.sqrt (w / (n : ℝ)) *
          Real.exp (-(kBVClassRate D vlo vhi * n / w ^ 2)) * ‖h2.toLp u‖) G ∧
      ‖R‖ ≤ kBVClassRemConst D vlo vhi / Real.sqrt (n : ℝ) *
        kBVClassRho D vlo vhi ^ (n / 2) *
          Real.exp (-(kBVClassRate D vlo vhi * n / w ^ 2)) * ‖h2.toLp u‖ := by
  have hc := killCnu_pos hD hvlo (hν.var_ge.trans hν.var_le)
  have hρ1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo (hν.var_ge.trans hν.var_le)
  have hgap := killGapConst_pos hc (by norm_num : (0 : ℝ) < 1 / 2)
  have hfac := kBV_window_factor_le hc hgap.le (by linarith : 0 < w)
    (kBVNormSq_nonneg u) n hn
  have hroot : Real.sqrt (kBVNormSq u) = ‖h2.toLp u‖ := by
    rw [← kBV_toLp_norm_sq h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hroot] at hfac
  obtain ⟨G, R, hGR, hG, hR⟩ := kBV_regLaw_n_decomposition hD hθ hvlo hν β ha hw hu h2 hsupp n hn
  refine ⟨G, R, hGR, kBVHasRep_mono hG ?_, hR.trans ?_⟩
  · have hC : 0 ≤ 8 * Real.pi * Real.sqrt w +
        8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi)) := by
      have hp : 0 < 1 - Real.sqrt (1 - killCnu D vlo vhi) := by linarith
      positivity
    refine (mul_le_mul_of_nonneg_left hfac hC).trans_eq ?_
    unfold kBVClassVarConst kBVClassRho kBVClassRemConst kBVClassRate
    rw [Real.sqrt_div (by linarith : 0 ≤ w)]
    ring
  · refine (mul_le_mul_of_nonneg_left hfac
      (pow_nonneg (Real.sqrt_nonneg (1 - killCnu D vlo vhi)) (n / 2))).trans_eq ?_
    unfold kBVClassRemConst kBVClassRho kBVClassRate
    ring

end
end PGM
