import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Rectangular Taylor approximation of two genuinely holomorphic variables -/

noncomputable section
open Complex Set Metric Filter Topology Finset Asymptotics
namespace PGM

def bivariateTaylorSum (F : ℂ → ℂ → ℂ) (N : ℕ) (q ζ : ℂ) : ℂ :=
  ∑ m ∈ range (N + 1), (m.factorial : ℂ)⁻¹ * ζ ^ m *
    complexTaylorSum (fun w : ℂ => iteratedDeriv m (F w) 0) (N + 1) 0 q

theorem norm_sub_bivariateTaylorSum_le {F : ℂ → ℂ → ℂ} {R S M : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.2 x.1) (ball 0 R ×ˢ ball 0 S))
    (hb : ∀ x ∈ ball (0 : ℂ) R ×ˢ ball 0 S, ‖F x.2 x.1‖ ≤ M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q ζ : ℂ}, q ∈ ball (0 : ℂ) (S / 2) →
      ζ ∈ ball (0 : ℂ) (R / 2) →
      ‖F q ζ - bivariateTaylorSum F N q ζ‖ ≤ C * (‖ζ‖ ^ (N + 1) + ‖q‖ ^ (N + 1)) := by
  let A : ℕ → ℂ → ℂ := fun m q => iteratedDeriv m (F q) 0
  let B : ℕ → ℝ := fun m => (m.factorial : ℝ) * M / (R / 2) ^ m
  have hdA (m : ℕ) : DifferentiableOn ℂ (A m) (ball 0 S) := by
    have ht := differentiableOn_iteratedDeriv_fst (isOpen_ball.prod isOpen_ball) hd m
    simpa only [A, Function.comp_apply] using!
      ht.comp ((differentiableOn_const (0 : ℂ)).prodMk differentiableOn_id)
        (fun _ hq => ⟨mem_ball_self hR, hq⟩)
  have hdz (q : ℂ) (hq : q ∈ ball (0 : ℂ) S) : DifferentiableOn ℂ (F q) (ball 0 R) :=
    fun ζ hζ => (differentiableAt_slice_fst (isOpen_ball.prod isOpen_ball) hd
      (show (ζ, q) ∈ ball 0 R ×ˢ ball 0 S from ⟨hζ, hq⟩)).differentiableWithinAt
  have hbA (m : ℕ) (q : ℂ) (hq : q ∈ ball (0 : ℂ) S) : ‖A m q‖ ≤ B m :=
    norm_iteratedDeriv_le_of_ball m hR (hdz q hq) (fun ζ hζ => hb (ζ, q) ⟨hζ, hq⟩)
  let L : ℝ := ((N + 1).factorial : ℝ) * M / (R / 4) ^ (N + 1)
  let K : ℝ := ∑ m ∈ range (N + 1), ‖(m.factorial : ℂ)⁻¹‖ * R ^ m *
    (((N + 1).factorial : ℝ) * B m / (S / 4) ^ (N + 1))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K, B]; positivity
  refine ⟨L + K, add_nonneg hL hK, ?_⟩
  intro q ζ hq hζ
  have hqS := ball_subset_ball (half_le_self hS.le) hq
  have hζR : ‖ζ‖ ≤ R := (mem_ball_zero_iff.mp hζ).le.trans (half_le_self hR.le)
  have hfirst := norm_sub_complexTaylorSum_le_of_ball (N + 1) hR (hdz q hqS)
    (fun w hw => hb (w, q) ⟨hw, hqS⟩) hζ
  simp only [sub_zero] at hfirst
  have hsecond : ‖complexTaylorSum (F q) (N + 1) 0 ζ - bivariateTaylorSum F N q ζ‖ ≤
      K * ‖q‖ ^ (N + 1) := by
    rw [complexTaylorSum, bivariateTaylorSum]
    simp only [sub_zero]
    rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    change (∑ m ∈ range (N + 1), ‖(m.factorial : ℂ)⁻¹ * ζ ^ m * A m q -
      (m.factorial : ℂ)⁻¹ * ζ ^ m * complexTaylorSum (A m) (N + 1) 0 q‖) ≤ _
    dsimp only [K]
    rw [sum_mul]
    apply sum_le_sum
    intro m _
    rw [← mul_sub, norm_mul, norm_mul, norm_pow]
    have ht := norm_sub_complexTaylorSum_le_of_ball (N + 1) hS (hdA m) (hbA m) hq
    simp only [sub_zero] at ht
    calc
      _ ≤ ‖(m.factorial : ℂ)⁻¹‖ * R ^ m *
          ((((N + 1).factorial : ℝ) * B m / (S / 4) ^ (N + 1)) * ‖q‖ ^ (N + 1)) := by
        apply mul_le_mul ?_ ht (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hζR m) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ‖F q ζ - complexTaylorSum (F q) (N + 1) 0 ζ‖ +
        ‖complexTaylorSum (F q) (N + 1) 0 ζ - bivariateTaylorSum F N q ζ‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * ‖ζ‖ ^ (N + 1) + K * ‖q‖ ^ (N + 1) := add_le_add hfirst hsecond
    _ ≤ (L + K) * (‖ζ‖ ^ (N + 1) + ‖q‖ ^ (N + 1)) := by
      nlinarith [mul_nonneg hK (pow_nonneg (norm_nonneg ζ) (N + 1)),
        mul_nonneg hL (pow_nonneg (norm_nonneg q) (N + 1))]

/-- The rectangular approximation keeps the requested order along small curves. -/
theorem bivariateTaylorSum_curve_isBigO {F : ℂ → ℂ → ℂ} {R S M : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.2 x.1) (ball 0 R ×ˢ ball 0 S))
    (hb : ∀ x ∈ ball (0 : ℂ) R ×ˢ ball 0 S, ‖F x.2 x.1‖ ≤ M)
    {q ζ : ℂ → ℂ} (hq : Tendsto q (𝓝 0) (𝓝 0)) (hζ : Tendsto ζ (𝓝 0) (𝓝 0))
    (hqo : q =O[𝓝 (0 : ℂ)] fun b => b) (hζo : ζ =O[𝓝 (0 : ℂ)] fun b => b) (N : ℕ) :
    (fun b => F (q b) (ζ b) - bivariateTaylorSum F N (q b) (ζ b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  obtain ⟨C, _, hC⟩ := norm_sub_bivariateTaylorSum_le hR hS hM hd hb N
  have he : (fun b => F (q b) (ζ b) - bivariateTaylorSum F N (q b) (ζ b))
      =O[𝓝 (0 : ℂ)] (fun b => ‖ζ b‖ ^ (N + 1) + ‖q b‖ ^ (N + 1)) := by
    apply IsBigO.of_bound C
    filter_upwards [hq.eventually (ball_mem_nhds (0 : ℂ) (half_pos hS)),
      hζ.eventually (ball_mem_nhds (0 : ℂ) (half_pos hR))] with b hqb hζb
    simpa only [Real.norm_of_nonneg (show 0 ≤ ‖ζ b‖ ^ (N + 1) + ‖q b‖ ^ (N + 1)
      from by positivity)] using hC hqb hζb
  exact he.trans ((hζo.norm_left.pow (N + 1)).add (hqo.norm_left.pow (N + 1)))

end PGM
