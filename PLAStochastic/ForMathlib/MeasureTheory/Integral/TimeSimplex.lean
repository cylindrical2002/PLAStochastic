import PLAStochastic.ForMathlib.MeasureTheory.Integral.RectangleAverage

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem lintegral_time_triangle_slice (F : ℝ × ℝ × ℝ → ℝ≥0∞)
    {v w : ℝ} (hv : 0<v) (hw : 0<w) :
    (∫⁻ T in Ioi (0:ℝ), (Ioo 0 (T-v)).indicator (fun w => F (v,w,T-v-w)) w)=
      ∫⁻ t in Ioi (0:ℝ), F (v,w,t) := by
  have hpoint (T : ℝ) : (Ioo 0 (T-v)).indicator (fun w => F (v,w,T-v-w)) w=
      (Ioi (v+w)).indicator (fun T => F (v,w,T-v-w)) T := by
    by_cases h : v+w<T
    · rw [indicator_of_mem (show w∈Ioo 0 (T-v) from ⟨hw,by linarith⟩),indicator_of_mem (show T∈Ioi (v+w) from h)]
    · rw [indicator_of_notMem (show w∉Ioo 0 (T-v) by intro h'; exact h (by linarith [h'.2])),indicator_of_notMem (show T∉Ioi (v+w) from h)]
  simp only [hpoint]
  rw [lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (show Ioi (v+w)⊆Ioi (0:ℝ) by intro T hT; exact lt_trans (add_pos hv hw) hT)]
  have hs : (fun t : ℝ => (v+w)+1*t) ⁻¹' Ioi (v+w)=Ioi (0:ℝ) := by
    ext t
    simp only [mem_preimage,mem_Ioi,one_mul]
    constructor <;> intro h <;> linarith
  have h := setLIntegral_affine_preimage_eq_div (fun T => F (v,w,T-v-w))
    (S := Ioi (v+w)) measurableSet_Ioi (v+w) (by norm_num : (1:ℝ)≠0)
  rw [hs] at h
  simpa only [abs_one,ENNReal.ofReal_one,div_one,one_mul,
    show ∀ t : ℝ, v+w+t-v-w=t by intro t; ring] using h.symm

/-- Tonelli and translation transform a positive time simplex into three independent positive times. -/
theorem lintegral_positive_time_simplex {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ T in Ioi (0:ℝ), ∫⁻ v in Ioi (0:ℝ), ∫⁻ w in Ioo (0:ℝ) (T-v), F (v,w,T-v-w))=
      ∫⁻ v in Ioi (0:ℝ), ∫⁻ w in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), F (v,w,t) := by
  let H : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    (Ioo 0 (p.1.1-p.1.2)).indicator (fun w => F (p.1.2,w,p.1.1-p.1.2-w)) p.2
  have hm : Measurable H := by
    have hs : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.2∈Ioo 0 (p.1.1-p.1.2)} := by
      simp only [mem_Ioo]
      measurability
    exact (hF.comp (f := fun p : (ℝ × ℝ) × ℝ => (p.1.2,p.2,p.1.1-p.1.2-p.2))
      (by fun_prop)).indicator hs
  have hi : Measurable (fun p : ℝ × ℝ => ∫⁻ w, H (p,w)) := hm.lintegral_prod_right'
  have he (T v : ℝ) : (∫⁻ w in Ioo 0 (T-v), F (v,w,T-v-w))=∫⁻ w, H ((T,v),w) :=
    (lintegral_indicator measurableSet_Ioo _).symm
  simp only [he]
  rw [lintegral_lintegral_swap hi.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hvM : Measurable (fun p : ℝ × ℝ => H ((p.1,v),p.2)) := hm.comp (by fun_prop)
  rw [lintegral_lintegral_swap hvM.aemeasurable,←lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro w
  by_cases hw : 0<w
  · rw [indicator_of_mem (show w∈Ioi (0:ℝ) from hw)]
    exact lintegral_time_triangle_slice F hv hw
  · rw [indicator_of_notMem (show w∉Ioi (0:ℝ) from hw)]
    calc
      _ = ∫⁻ _T in Ioi (0:ℝ), (0:ℝ≥0∞) := by
        apply lintegral_congr
        intro T
        exact indicator_of_notMem (show w∉Ioo 0 (T-v) by intro h; exact hw h.1) _
      _ = 0 := by simp

end BrownianAffine
