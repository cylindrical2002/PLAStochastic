import PLAStochastic.Index.GEP.Kernel.Insertion.CoefficientNear

/-! # Arithmetic of the original near-critical AL scale -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

/-- The near-critical hypothesis pays for the slope-window length. -/
theorem krInsertion_window_measure {S : Set ℝ} {w A : ℝ} (hw : 0 < w) (hA : 0 ≤ A)
    (hS : ∀ a ∈ S, |a-1| ≤ A/w) : volume.real S ≤ 2*A/w := by
  have hi : S ⊆ Icc (1-A/w) (1+A/w) := by
    intro a ha
    have hh := abs_le.mp (hS a ha)
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have he : volume.real (Icc (1-A/w) (1+A/w)) = 2*A/w := by
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith [div_nonneg hA hw.le] : 0 ≤ 1+A/w-(1-A/w))]
    ring
  exact (measureReal_mono hi (by simp)).trans_eq he

/-- The exponentially small row error also fits the inverse-square-root trace budget. -/
theorem krInsertion_exp_le_trace {w c T : ℝ} (hw : 1 ≤ w) (hc : 0 < c) (hT : 1/c ≤ T) :
    Real.exp (-c*w) ≤ T/Real.sqrt w := by
  have hw0 : 0 < w := by linarith
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hsw : Real.sqrt w ≤ w := Real.sqrt_le_self_iff.mpr (Or.inr hw)
  have he : c*Real.sqrt w ≤ Real.exp (c*w) := by
    have hh := Real.add_one_le_exp (c*w)
    nlinarith
  have hh : Real.exp (-c*w) ≤ (1/c)/Real.sqrt w := by
    apply (le_div_iff₀ hs).2
    rw [one_div,neg_mul,Real.exp_neg]
    apply (mul_le_mul_iff_right₀ (mul_pos hc (Real.exp_pos (c*w)))).mp
    field_simp
    nlinarith
  exact hh.trans (div_le_div_of_nonneg_right hT hs.le)

set_option maxHeartbeats 1200000 in
/-- Compressing the proved budgets loses only a fixed power of the near parameter.
The first bound is w²√w before the physical reward's 1/C normalization. -/
theorem krInsertion_algebra {w U T M μ D V B O P R W ST e c : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hμ : 0 ≤ μ) (hμb : μ ≤ 2*U/w) (hD : 0 ≤ D) (hDT : D ≤ T)
    (hV0 : 0 ≤ V) (hB0 : 0 ≤ B) (hO0 : 0 ≤ O) (hP0 : 0 ≤ P)
    (hR0 : 0 ≤ R) (hW0 : 0 ≤ W) (hST0 : 0 ≤ ST) (_he0 : 0 ≤ e)
    (hV : V ≤ T*U*Real.sqrt w) (hB : B ≤ T*U*(1+Real.log w))
    (hO : O ≤ T*U*w) (hP : P ≤ T*U^2/Real.sqrt w)
    (hR : R ≤ T*U*Real.exp (-c*w)) (hW : W ≤ T*U^2*w)
    (hST : ST ≤ T*w^2*Real.exp (-c*w)) (he : e ≤ T)
    (htr : Real.exp (-c*w) ≤ T/Real.sqrt w) :
    (M*e*(1+O^2*W))*(μ*(4*V*B+8*D*V)+4*(2*P+8*R)) ≤
      128*M*T^6*U^7*w^2*Real.sqrt w*(1+Real.log w) ∧
    (M*e*(1+O^2*W))*(μ*(8*R*O+8*R+ST)) ≤
      68*M*T^6*U^7*w^4*Real.exp (-c*w) := by
  have hw0 : 0 < w := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hsq : Real.sqrt w^2=w := Real.sq_sqrt hw0.le
  have hlog : 1 ≤ 1+Real.log w := by linarith [Real.log_nonneg hw]
  have hlog0 : 0 ≤ 1+Real.log w := by linarith
  have hTU : 1 ≤ T*U := one_le_mul_of_one_le_of_one_le hT hU
  have hUg : 1 ≤ U*(1+Real.log w) := one_le_mul_of_one_le_of_one_le hU hlog
  have hcube : 1 ≤ T^3*U^4*w^3 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hU)) (one_le_pow₀ hw)
  have hN : M*e*(1+O^2*W) ≤ 2*M*T^4*U^4*w^3 := by
    calc
      _ ≤ M*T*(1+(T*U*w)^2*(T*U^2*w)) := by gcongr
      _ = M*T*(1+T^3*U^4*w^3) := by ring
      _ ≤ M*T*(2*(T^3*U^4*w^3)) := by gcongr; linarith
      _ = _ := by ring
  have hD' : D ≤ T*U*(1+Real.log w) := by
    apply hDT.trans
    nlinarith [mul_le_mul_of_nonneg_left hUg hT0]
  have hcontinuous : 4*V*B+8*D*V ≤ 12*T^2*U^2*Real.sqrt w*(1+Real.log w) := by
    have hh := add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hV (show (0 : ℝ) ≤ 4 by norm_num)) hB hB0 (by positivity))
      (mul_le_mul (mul_le_mul_of_nonneg_left hD' (show (0 : ℝ) ≤ 8 by norm_num)) hV hV0 (by positivity))
    exact hh.trans_eq (by ring)
  have hpart : μ*(4*V*B+8*D*V) ≤ 24*T^2*U^3*(1+Real.log w)/Real.sqrt w := by
    have hh := mul_le_mul hμb hcontinuous (by positivity) (by positivity)
    apply hh.trans_eq
    field_simp
    nlinarith [hsq]
  have hP' : P ≤ T^2*U^2/Real.sqrt w := by
    apply hP.trans
    gcongr
    nlinarith
  have hR' : R ≤ T^2*U^2/Real.sqrt w := by
    apply (hR.trans (mul_le_mul_of_nonneg_left htr (by positivity))).trans
    have hh : T*U*(T/Real.sqrt w) = T^2*U/Real.sqrt w := by ring
    rw [hh]
    gcongr
    nlinarith
  have htrace : 4*(2*P+8*R) ≤ 40*T^2*U^3*(1+Real.log w)/Real.sqrt w := by
    have hh : 4*(2*P+8*R) ≤ 40*(T^2*U^2/Real.sqrt w) := by linarith
    apply hh.trans
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [mul_le_mul_of_nonneg_left hUg (show 0 ≤ 40*T^2*U^2 by positivity)]
  have hLip : μ*(4*V*B+8*D*V)+4*(2*P+8*R) ≤
      64*T^2*U^3*(1+Real.log w)/Real.sqrt w :=
    (add_le_add hpart htrace).trans_eq (by ring)
  have hRO : R*O ≤ T^2*U^2*w^2*Real.exp (-c*w) := by
    have hh := mul_le_mul hR hO hO0 (by positivity)
    apply hh.trans
    have hww : w ≤ w^2 := by nlinarith
    calc T*U*Real.exp (-c*w)*(T*U*w) = T^2*U^2*w*Real.exp (-c*w) := by ring
         _ ≤ _ := by gcongr
  have hR'' : R ≤ T^2*U^2*w^2*Real.exp (-c*w) := by
    apply hR.trans
    have hb : T*U ≤ T^2*U^2*w^2 := by
      have htuw : 1 ≤ T*U*w^2 := one_le_mul_of_one_le_of_one_le hTU (one_le_pow₀ hw)
      nlinarith [mul_le_mul_of_nonneg_left htuw (show 0 ≤ T*U by positivity)]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
  have hST' : ST ≤ T^2*U^2*w^2*Real.exp (-c*w) := by
    apply hST.trans
    gcongr
    nlinarith [one_le_mul_of_one_le_of_one_le hT (one_le_pow₀ (n := 2) hU)]
  have herr : μ*(8*R*O+8*R+ST) ≤ 34*T^2*U^3*w*Real.exp (-c*w) := by
    have hb : 8*R*O+8*R+ST ≤ 17*(T^2*U^2*w^2*Real.exp (-c*w)) := by nlinarith
    have hh := mul_le_mul hμb hb (by positivity) (by positivity)
    apply hh.trans_eq
    field_simp
    ring
  constructor
  · have hh := mul_le_mul hN hLip (by positivity) (by positivity)
    apply hh.trans_eq
    field_simp
    nlinarith [hsq]
  · exact (mul_le_mul hN herr (by positivity) (by positivity)).trans_eq (by ring)


/-- A single class constant dominates the finitely many row constants. -/
theorem krInsertion_majorant_exists (D Cv Cr Cb Co Cp Cw Ks c : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ D ≤ T ∧ Real.exp 1 ≤ T ∧ 1/c ≤ T ∧
      6*Real.exp 3*Cv ≤ T ∧ 2*Real.exp 5*Cr ≤ T ∧ Real.exp 3*Cb ≤ T ∧
      Real.exp 3*Co ≤ T ∧ Real.exp 3*Cp ≤ T ∧ Real.exp 3*Cw ≤ T ∧ Real.exp 1*Ks ≤ T := by
  let T := max 1 (max D (max (Real.exp 1) (max (1/c) (max (6*Real.exp 3*Cv)
    (max (2*Real.exp 5*Cr) (max (Real.exp 3*Cb) (max (Real.exp 3*Co)
      (max (Real.exp 3*Cp) (max (Real.exp 3*Cw) (Real.exp 1*Ks))))))))))
  refine ⟨T,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [T,le_max_iff,le_refl,or_true,true_or]

end
end PGM
