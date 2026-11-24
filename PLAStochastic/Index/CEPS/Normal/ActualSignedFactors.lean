import PLAStochastic.Index.CEPS.Normal.ActualJointFactors
import PLAStochastic.Index.CEPS.Normal.HolomorphyNonzero

/-! # Signed Morse factor data on the full actual discount preimage -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain
def normalMorseSet {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (μ : ℂ) : Set ℂ :=
  ball 0 dom.rmax ∩ {r | ‖cepsMorseDiscount D θ ρW μ r‖ < dom.q₀}
end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cepsNormal_morseSet_open (μ : ℂ) : IsOpen (dom.normalMorseSet ρW μ) := by
  exact isOpen_ball.inter (isOpen_lt (by unfold cepsMorseDiscount; fun_prop) continuous_const)

include hW hθ hD in
theorem cepsMorseNormalData_Q_differentiableOn_full {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => (cepsMorseNormalData D θ ρW μ x.1).Q x.2)
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hQ := cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμ
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (cepsMorseDiscount D θ ρW μ x.1, x.2))
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
    unfold cepsMorseDiscount
    fun_prop
  refine hQ.comp (f := fun x : ℂ × ℂ => (cepsMorseDiscount D θ ρW μ x.1, x.2)) hp ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · change ‖cepsMorseMin D θ ρW μ + x.1 ^ 2 - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2
    rw [add_sub_cancel_left, norm_pow]
    exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp hx.1.1) (norm_nonneg _) (by norm_num)
  · apply mem_ball_zero_iff.mpr
    have := mem_ball_zero_iff.mp hx.2
    have := dom.c₀_le; have := dom.ρA_pos; linarith

include hW hθ hD in
theorem cepsMorse_canonL_differentiableOn_full {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      dom.canonL ρW μ (cepsMorseDiscount D θ ρW μ x.1) x.2)
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hL := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (x.2, cepsMorseDiscount D θ ρW μ x.1))
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
    unfold cepsMorseDiscount
    fun_prop
  refine hL.comp (f := fun x : ℂ × ℂ => (x.2, cepsMorseDiscount D θ ρW μ x.1)) hp ?_
  intro x hx
  exact ⟨by have := mem_ball_zero_iff.mp hx.2; linarith [re_le_norm x.2, dom.c₀_pos], hx.1.2⟩

include hW hθ hD in
theorem cepsMorseNormalData_normalG_differentiableOn_full {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    (l : ℂ) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (cepsMorseNormalData D θ ρW μ x.1).normalG (dom.canonL ρW) μ
        (cepsMorseDiscount D θ ρW μ x.1) l x.2)
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hQ := cepsMorseNormalData_Q_differentiableOn_full dom hW hθ hD hμ'
  have hL := cepsMorse_canonL_differentiableOn_full dom hW hθ hD hμ
  exact (((differentiableOn_snd.neg.mul_const l).cexp).mul hQ).mul
    ((hL.const_mul (-2 : ℂ)).cexp)

include hW hθ hD in
theorem cepsMorseNormalData_root_maps_full {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    MapsTo (fun r => (cepsMorseNormalData D θ ρW μ r).βp)
      (dom.normalMorseSet ρW μ) (ball 0 (dom.c₀ / 2)) ∧
    MapsTo (fun r => (cepsMorseNormalData D θ ρW μ r).βm)
      (dom.normalMorseSet ρW μ) (ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  constructor <;> intro r hr <;> apply mem_ball_zero_iff.mpr
  · have hb := cepsMorseRoot_norm_le dom hW hθ hD hμ' (mem_ball_zero_iff.mp hr.1)
    change ‖cepsMorseRoot D θ ρW μ r‖ < dom.c₀ / 2
    linarith [dom.c₀_pos]
  · have hn : ‖-r‖ < dom.rmax := by simpa using mem_ball_zero_iff.mp hr.1
    have hb := cepsMorseRoot_norm_le dom hW hθ hD hμ' hn
    change ‖cepsMorseRoot D θ ρW μ (-r)‖ < dom.c₀ / 2
    linarith [dom.c₀_pos]

include hW hθ hD in
theorem cepsMorseNormalData_holomorphicAt_of_dslope_ne {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {r t : ℂ} (hr : r ∈ dom.normalMorseSet ρW μ) (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ}
    (hS : dslope ((cepsMorseNormalData D θ ρW μ r).normalG (dom.canonL ρW) μ
      (cepsMorseDiscount D θ ρW μ r) l)
        (cepsMorseNormalData D θ ρW μ r).βm (cepsMorseNormalData D θ ρW μ r).βp ≠ 0) :
    DifferentiableAt ℂ (fun r' => (cepsMorseNormalData D θ ρW μ r').regularEntrance
      (dom.canonL ρW) μ (cepsMorseDiscount D θ ρW μ r') l t) r ∧
    DifferentiableAt ℂ (fun r' => (cepsMorseNormalData D θ ρW μ r').regularBridge
      (dom.canonL ρW) μ (cepsMorseDiscount D θ ρW μ r') l) r := by
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let q := cepsMorseDiscount D θ ρW (μ : ℂ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hΘ := cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ'
  have hbp : DifferentiableOn ℂ (fun r => (A r).βp) U := hΘ.mono inter_subset_left
  have hbm : DifferentiableOn ℂ (fun r => (A r).βm) U := by
    exact (hΘ.comp (f := fun r : ℂ => -r) differentiableOn_id.neg
      (fun r hr => mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr))).mono
        inter_subset_left
  obtain ⟨hbpmap, hbmmap⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have htA : t ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQt := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hr.2.le htA
  obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_holomorphic_near_of_dslope_ne
    (A := A) (L := dom.canonL ρW) (μ := (μ : ℂ)) (q := q) (t := fun _ => t) hU
    (cepsMorseNormalData_Q_differentiableOn_full dom hW hθ hD hμ')
    (cepsMorse_canonL_differentiableOn_full dom hW hθ hD hμ)
    hbp hbm (differentiableOn_const t) hbpmap hbmmap
    (fun _ _ => mem_ball_zero_iff.mpr ht) hr hS hQt
  exact ⟨(hE r (mem_ball_self hε)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε)),
    (hB r (mem_ball_self hε)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))⟩

end PGM
