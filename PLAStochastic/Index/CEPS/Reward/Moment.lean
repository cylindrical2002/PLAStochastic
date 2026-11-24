import PLAStochastic.Index.CEPS.Reward.Exponential

/-! # Exponentially weighted reward moments and finite convolution intervals -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def rewardMoment (β : ℂ) (b : ℝ → ℂ) : ℂ :=
  ∫ z in Ioi (0 : ℝ), cexp (β * z) * b z

variable {b : ℝ → ℂ} {B θ r : ℝ} {β : ℂ}

theorem integrableOn_rewardMoment_tail (hb : Measurable b)
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z))
    (hβ : ‖β‖ ≤ r) (hr : r < θ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun z : ℝ => cexp (β * z) * b z) (Ioi x) := by
  have hI : IntegrableOn (fun z : ℝ => B * Real.exp ((r - θ) * z)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  have hmeas : Measurable (fun z : ℝ => cexp (β * z) * b z) :=
    (by fun_prop : Measurable (fun z : ℝ => cexp (β * z))).mul hb
  refine hI.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun z hz => ?_)
  have hz0 : 0 ≤ z := hx.trans hz.le
  rw [norm_mul, norm_cexp_mul_ofReal', neg_neg]
  calc
    _ ≤ Real.exp (r * z) * (B * Real.exp (-θ * z)) :=
      mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        ((re_le_norm _).trans hβ) hz0)) (hB z hz0) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; congr 2; ring

theorem norm_rewardMoment_tail_le (hb : Measurable b)
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z))
    (hβ : ‖β‖ ≤ r) (hr : r < θ) {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ z in Ioi x, cexp (β * z) * b z‖ ≤
      B / (θ - r) * Real.exp (-(θ - r) * x) := by
  have hI : IntegrableOn (fun z : ℝ => B * Real.exp ((r - θ) * z)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  calc
    _ ≤ ∫ z in Ioi x, ‖cexp (β * z) * b z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in Ioi x, B * Real.exp ((r - θ) * z) := by
      apply integral_mono_ae (integrableOn_rewardMoment_tail hb hB hβ hr hx).norm hI
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun z hz => ?_)
      have hz0 : 0 ≤ z := hx.trans hz.le
      dsimp only
      rw [norm_mul, norm_cexp_mul_ofReal', neg_neg]
      calc
        _ ≤ Real.exp (r * z) * (B * Real.exp (-θ * z)) :=
          mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            ((re_le_norm _).trans hβ) hz0)) (hB z hz0) (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x,
        show r - θ = -(θ - r) by ring, div_neg]
      ring

theorem rewardMoment_split (hb : Measurable b)
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z))
    (hβ : ‖β‖ ≤ r) (hr : r < θ) {x : ℝ} (hx : 0 ≤ x) :
    rewardMoment β b = (∫ z in Ioo 0 x, cexp (β * z) * b z) +
      ∫ z in Ioi x, cexp (β * z) * b z := by
  have hu : Ioi (0 : ℝ) = Ioc 0 x ∪ Ioi x := by
    ext z
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hz
      exact (le_or_gt z x).elim (fun h => Or.inl ⟨hz, h⟩) Or.inr
    · rintro (⟨hz, _⟩ | hz)
      · exact hz
      · exact hx.trans_lt hz
  have hi := integrableOn_rewardMoment_tail hb hB hβ hr (x := 0) le_rfl
  have hd : Disjoint (Ioc (0 : ℝ) x) (Ioi x) :=
    disjoint_left.mpr fun _ h₁ h₂ => not_lt_of_ge h₁.2 h₂
  rw [rewardMoment, hu, setIntegral_union hd
    measurableSet_Ioi (hi.mono_set (fun _ h => h.1))
    (hi.mono_set (fun _ h => hx.trans_lt h)), integral_Ioc_eq_integral_Ioo]

/-- Convolution with a supported source is an ordinary finite-interval integral. -/
theorem convC_halfLine_eq_interval {u : ℝ → ℂ} (hu : HalfBdd u) (b : ℝ → ℂ)
    (x : ℝ) :
    convC u (halfLine b) x = ∫ z in Ioo 0 x, u (x - z) * b z := by
  rw [convC_comm, convC, ← integral_Icc_eq_integral_Ioo]
  calc
    _ = ∫ z in Icc 0 x, halfLine b z * u (x - z) := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro z hz
      simp only [mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz
      · rw [halfLine_of_neg _ hz, zero_mul]
      · rw [hu.eq_zero (x - z) (by linarith), mul_zero]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      dsimp only
      rw [halfLine_of_nonneg _ hz.1]
      ring

end PGM.WienerHopf
