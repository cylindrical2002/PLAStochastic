import PLAStochastic.Index.CEPS.Normal.SlopeCongr

/-! # Exact cancellation of a quadratic scale in removable spatial slopes -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

theorem cepsNormal_second_dslope_scale_factor {f g : ℂ → ℂ} {c a b t : ℂ}
    (hc : c ≠ 0) {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (he : EqOn (fun x => f (c * x)) (fun x => c ^ 2 * g x) U)
    (ha : a ∈ U) (hb : b ∈ U) (ht : t ∈ U)
    (hf : DifferentiableAt ℂ f (c * a))
    (hfS : DifferentiableAt ℂ (dslope f (c * a)) (c * b)) :
    dslope (dslope f (c * a)) (c * b) (c * t) = dslope (dslope g a) b t := by
  have hga := (hg a ha).differentiableAt (hU.mem_nhds ha)
  have hgS := ((differentiableOn_dslope (hU.mem_nhds ha)).mpr hg b hb).differentiableAt
    (hU.mem_nhds hb)
  have hs := second_dslope_comp_const_mul hc a b t hf hfS
  have heS := cepsNormal_second_dslope_eq_of_eqOn hU he ha hb ht
  have hm := cepsNormal_second_dslope_const_mul (c ^ 2) (t := t) hga hgS
  rw [hs, hm] at heS
  exact mul_left_cancel₀ (pow_ne_zero 2 hc) heS

end PGM
