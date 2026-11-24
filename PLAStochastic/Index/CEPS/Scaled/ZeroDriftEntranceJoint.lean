import PLAStochastic.Index.CEPS.Scaled.ZeroDriftBridgeJoint
import PLAStochastic.Index.CEPS.Scaled.ZeroDriftLiftNumerator
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance

/-! # Actual zero-drift marked entrance joint holomorphy through the origin -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledZeroDriftLiftMarkPrefactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r : ℂ) : ℂ :=
  exp (dom.canonL ρW 0 ((b * r) ^ 2) ((b * r) ^ 2)) /
    cepsQ D θ ρW 0 ((b * r) ^ 2) ((b * r) ^ 2)

def cepsScaledZeroDriftLiftEntranceNumerator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r : ℂ) : ℂ :=
  -cepsScaledZeroDriftLiftMarkPrefactor dom ρW b r * cepsScaledZeroDriftLiftNumerator dom ρW b r

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem cepsScaledZeroDriftLift_mark_discount_bounds {R : ℝ} (hR : 0 < R) {b r : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)) (hr : r ∈ ball (0 : ℂ) R) :
    ‖(b * r) ^ 2‖ < dom.q₀ ∧ ‖(b * r) ^ 2‖ < dom.c₀ / 2 := by
  have hn := mem_ball_zero_iff.mp hr
  have hbR := (mem_ball_zero_iff.mp hb).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhR := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + R))).mp hbR
  have hbr : ‖b‖ * ‖r‖ < dom.rmax / 2 := by nlinarith [norm_nonneg b]
  have hτ := mem_ball_zero_iff.mp (cepsScaledZeroDriftLift_marker_mem dom hD hR hb hr)
  have hbS := (mem_ball_zero_iff.mp hb).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hS := zeroDriftLiftSpatialRadius_pos dom hD hR
  have hhS := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + dom.zeroDriftLiftSpatialRadius R))).mp hbS
  have hqS : ‖b‖ * ‖b * r ^ 2‖ < dom.c₀ / 2 := by nlinarith [norm_nonneg b]
  constructor
  · rw [norm_pow, norm_mul, dom.q₀_def]
    nlinarith [mul_nonneg (norm_nonneg b) (norm_nonneg r), dom.rmax_pos]
  · have he : (b * r) ^ 2 = b * (b * r ^ 2) := by ring
    rw [he, norm_mul]
    exact hqS

include hW hθ hD in
theorem cepsScaledZeroDriftLiftMarkPrefactor_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftMarkPrefactor dom ρW x.1 x.2)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) := by
  let U := ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R) ×ˢ ball (0 : ℂ) R
  let q : ℂ × ℂ → ℂ := fun x => (x.1 * x.2) ^ 2
  have hp : DifferentiableOn ℂ (fun x => (q x, q x)) U := by dsimp [q]; fun_prop
  have hμ : ‖(0 : ℂ)‖ ≤ dom.μ₀ := by simpa using dom.μ₀_pos.le
  have hbounds : ∀ x ∈ U, ‖q x‖ < dom.q₀ ∧ ‖q x‖ < dom.c₀ / 2 :=
    fun x hx => cepsScaledZeroDriftLift_mark_discount_bounds dom hD hR hx.1 hx.2
  have hQ := (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμ).comp
    (f := fun x => (q x, q x)) hp (by
      intro x hx
      obtain ⟨hq, hζ⟩ := hbounds x hx
      refine ⟨?_, mem_ball_zero_iff.mpr ?_⟩
      change ‖q x - cepsMorseMin D θ ρW 0‖ < dom.rmax ^ 2
      rw [(cepsMorseMin_zero_jets hW hθ hD).1, sub_zero]
      exact hq.trans_le (by rw [dom.q₀_def]; nlinarith [sq_nonneg dom.rmax])
      have := dom.c₀_le
      have := dom.ρA_pos
      linarith)
  have hL : DifferentiableOn ℂ (fun x => dom.canonL ρW 0 (q x) (q x)) U := by
    intro x hx
    obtain ⟨hq, hζ⟩ := hbounds x hx
    exact ((dom.differentiableAt_canonL_qz hW hθ hD
      (show |(0 : ℝ)| ≤ dom.μ₀ by simpa using dom.μ₀_pos.le) hq
      ((re_le_norm _).trans_lt (hζ.trans (half_lt_self dom.c₀_pos)))).comp x
        ((hp x hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx))).differentiableWithinAt
  have hQ0 : ∀ x ∈ U, cepsQ D θ ρW 0 (q x) (q x) ≠ 0 := by
    intro x hx
    obtain ⟨hq, hζ⟩ := hbounds x hx
    exact CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ hq.le
      (mem_ball_zero_iff.mpr (by have := dom.c₀_le; have := dom.ρA_pos; linarith))
  exact hL.cexp.mul (hQ.inv hQ0)

include hW hθ hD in
theorem cepsScaledZeroDriftLiftEntranceNumerator_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftEntranceNumerator dom ρW x.1 x.2)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) :=
  (cepsScaledZeroDriftLiftMarkPrefactor_differentiableOn dom hW hθ hD hR).neg.mul
    (cepsScaledZeroDriftLiftNumerator_differentiableOn dom hW hθ hD hR)

include hW hθ hD in
theorem cepsScaledZeroDriftLiftEntranceNumerator_even {R : ℝ} (hR : 0 < R) {b r : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)) (hr : r ∈ ball (0 : ℂ) R) :
    cepsScaledZeroDriftLiftEntranceNumerator dom ρW b (-r) =
      cepsScaledZeroDriftLiftEntranceNumerator dom ρW b r := by
  unfold cepsScaledZeroDriftLiftEntranceNumerator
  rw [cepsScaledZeroDriftLiftNumerator_even dom hW hθ hD hR hb hr]
  unfold cepsScaledZeroDriftLiftMarkPrefactor
  rw [mul_neg, neg_sq]

theorem cepsScaledZeroDriftLiftEntrance_sqrt_eq_surrogate (N : ℕ) (b z : ℂ) :
    cepsScaledZeroDriftLiftEntranceNumerator dom ρW b (sqrt z) /
      cepsScaledZeroDriftLiftDenominator dom ρW b (sqrt z) =
        cepsScaledSurrogateEntrance dom ρW N 0 z b := by
  unfold cepsScaledZeroDriftLiftEntranceNumerator cepsScaledZeroDriftLiftMarkPrefactor
    cepsScaledZeroDriftLiftNumerator cepsScaledSurrogateEntrance
  rw [cepsScaledZeroDriftLiftG_eq_surrogate dom (ρW := ρW) N, sqrt_sq_eq,
    cepsScaledZeroDriftLiftDenominator_sqrt_eq_surrogate dom (ρW := ρW) N]
  simp only [cepsScaledSignedRoot_zeroDrift_eq_chart, neg_one_mul, one_mul,
    ofReal_zero, mul_zero, cepsCanonDriftTaylor_zero, cepsComplexScaledDiscount,
    add_zero, mul_one]
  rw [mul_pow, sqrt_sq_eq]
  simp only [div_eq_mul_inv, mul_inv]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_zeroDrift_holomorphic_near_joint_origin
    {m : ℕ} {η M : ℝ} (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 1 ≤ m) (N : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.zeroDriftKernelScaleRadius 1)
      (dom.surrogateRegularScaleRadius 0 M 0 0))) :
    ∃ ε > 0, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateEntrance dom ρW N 0 x.2 x.1)
      (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
  have hbL := ball_subset_ball (min_le_left _ _) hb
  have hbS := ball_subset_ball (min_le_right _ _) hb
  have hD0 : cepsScaledZeroDriftLiftDenominator dom ρW b 0 ≠ 0 := by
    have he := cepsScaledZeroDriftLiftDenominator_sqrt_eq_surrogate dom (ρW := ρW) 0 b 0
    rw [sqrt_zero] at he
    rw [he]
    exact cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM 0 (by simpa using hm)
      0 (by simp) hbS
  obtain ⟨ε, hε, hq⟩ := cepsNormal_joint_even_quotient_near_origin
    (F := cepsScaledZeroDriftLiftEntranceNumerator dom ρW)
    (S := cepsScaledZeroDriftLiftDenominator dom ρW) isOpen_ball (by norm_num : (0 : ℝ) < 1)
    (cepsScaledZeroDriftLiftEntranceNumerator_differentiableOn dom hW hθ hD (by norm_num))
    (cepsScaledZeroDriftLiftDenominator_differentiableOn dom hW hθ hD (by norm_num))
    (fun b hb' r hr => cepsScaledZeroDriftLiftEntranceNumerator_even dom hW hθ hD (by norm_num) hb' hr)
    (fun b _ r _ => cepsScaledZeroDriftLiftDenominator_even dom b r) hbL hD0
  refine ⟨ε, hε, hq.congr ?_⟩
  intro x _
  exact (cepsScaledZeroDriftLiftEntrance_sqrt_eq_surrogate dom (ρW := ρW) N x.1 x.2).symm

end PGM
