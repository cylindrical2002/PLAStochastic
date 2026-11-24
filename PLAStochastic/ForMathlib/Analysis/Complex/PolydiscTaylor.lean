import PLAStochastic.ForMathlib.Analysis.Complex.PolydiscDFT
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Uniform box Taylor expansions of functions analytic and bounded on a polydisc

For `F : (Fin d → ℂ) → ℂ` analytic at every point of the sup-norm ball (polydisc)
`ball p₀ R` and bounded by `M` there:

* `polydiscTaylorCoeff F p₀ α`: the canonical coordinate Taylor coefficients, read from the
  iterated derivatives `(n!)⁻¹ Dⁿ F(p₀)` (no choice of a power series);
* `iteratedDeriv_line_eq_iteratedFDeriv`: on complex lines, `∂ₜⁿ F(p₀ + t v)|₀ = Dⁿ F(p₀)(v,…,v)`;
* `polydiscTaylorCoeff_eq_grid`: each coefficient is a finite Fourier average of line
  derivatives (used for parametric analyticity and measurability);
* `norm_polydiscTaylorCoeff_le`: `‖C α‖ ≤ M (2/R)^{|α|}`;
* `norm_sub_polydiscTaylorBox_le`: for `‖x‖ ≤ R/4`,
  `‖F(p₀ + x) - ∑_{α ∈ box N} C α x^α‖ ≤ K(d,N) M (‖x‖/R)^{N+1}` with
  `K(d,N) = (N+1)! 4^{N+1} + (N+1)^d 2^{N+1}`.

The estimates use one-variable Cauchy estimates along complex lines and the finite Fourier
extraction of `PolydiscDFT`; no several-variable Cauchy formula is needed.
-/

noncomputable section
open Complex Finset Metric
namespace PGM

variable {d : ℕ}

/-- The canonical Taylor series `(n!)⁻¹ Dⁿ F(p₀)` of `F` at `p₀`. -/
def polydiscTaylorSeries (F : (Fin d → ℂ) → ℂ) (p₀ : Fin d → ℂ) :
    FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ :=
  fun n => ((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n F p₀

/-- The canonical coordinate Taylor coefficients of `F` at `p₀`. -/
def polydiscTaylorCoeff (F : (Fin d → ℂ) → ℂ) (p₀ : Fin d → ℂ) (α : Fin d → ℕ) : ℂ :=
  finiteCoordinateTaylorCoeff (polydiscTaylorSeries F p₀) α

theorem polydiscTaylorSeries_apply_diag (F : (Fin d → ℂ) → ℂ) (p₀ : Fin d → ℂ) (n : ℕ)
    (x : Fin d → ℂ) :
    polydiscTaylorSeries F p₀ n (fun _ => x) =
      (n.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ n F p₀ (fun _ => x) := by
  simp [polydiscTaylorSeries]

/-- The homogeneous Taylor polynomial of degree `n` as a box polynomial. -/
theorem polydiscTaylorSeries_apply_diag_eq_box (F : (Fin d → ℂ) → ℂ) (p₀ : Fin d → ℂ) (n : ℕ)
    (x : Fin d → ℂ) :
    polydiscTaylorSeries F p₀ n (fun _ => x) = ∑ α ∈ finiteCoordinateTaylorBox d n,
      (if (∑ i, α i) = n then polydiscTaylorCoeff F p₀ α else 0) * ∏ i, x i ^ α i := by
  rw [multilinear_diagonal_eq_coordinate_box]
  refine sum_congr rfl fun α _ => ?_
  split_ifs <;> simp [polydiscTaylorCoeff]

/-- **Line derivatives.** Along a complex line through an analyticity point, the one-variable
derivatives are the diagonal values of the iterated Fréchet derivatives. -/
theorem iteratedDeriv_line_eq_iteratedFDeriv {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ}
    (hF : AnalyticAt ℂ F p₀) (v : Fin d → ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => F (p₀ + t • v)) 0 = iteratedFDeriv ℂ n F p₀ (fun _ => v) := by
  set F' : (Fin d → ℂ) → ℂ := fun w => F (p₀ + w) with hF'
  set s : Set (Fin d → ℂ) := {w | AnalyticAt ℂ F' w}
  have hs : IsOpen s := isOpen_analyticAt ℂ F'
  have h0 : (0 : Fin d → ℂ) ∈ s := by
    show AnalyticAt ℂ (fun w => F (p₀ + w)) 0
    have h1 : AnalyticAt ℂ F (p₀ + 0) := by rwa [add_zero]
    exact h1.comp (analyticAt_const.add analyticAt_id)
  set L : ℂ →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ v
  have hL0 : L 0 = 0 := map_zero L
  have hLs : L 0 ∈ s := by rw [hL0]; exact h0
  have han : AnalyticOnNhd ℂ F' s := fun _ hw => hw
  have hcd : ContDiffOn ℂ (n : WithTop ℕ∞) F' s := han.contDiffOn hs.uniqueDiffOn
  have hpre : IsOpen (L ⁻¹' s) := hs.preimage L.continuous
  have hcomp := L.iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn hpre.uniqueDiffOn hLs
    (i := n) le_rfl
  have hmem : (0 : ℂ) ∈ L ⁻¹' s := hLs
  rw [iteratedFDerivWithin_of_isOpen n hpre hmem, hL0,
    iteratedFDerivWithin_of_isOpen n hs h0] at hcomp
  have hfun : (fun t : ℂ => F (p₀ + t • v)) = F' ∘ L := by
    funext t
    simp [F', L]
  have hshift : iteratedFDeriv ℂ n F' 0 = iteratedFDeriv ℂ n F p₀ := by
    rw [hF', iteratedFDeriv_comp_add_left' n p₀]
    simp only [add_zero]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun, hcomp,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hshift]
  simp [L]

/-- Diagonal Taylor terms along lines. -/
theorem polydiscTaylorSeries_apply_diag_eq_line {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ}
    (hF : AnalyticAt ℂ F p₀) (n : ℕ) (x : Fin d → ℂ) :
    polydiscTaylorSeries F p₀ n (fun _ => x) =
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun t : ℂ => F (p₀ + t • x)) 0 := by
  rw [polydiscTaylorSeries_apply_diag, iteratedDeriv_line_eq_iteratedFDeriv hF]

theorem differentiableAt_line (p₀ v : Fin d → ℂ) (t : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => p₀ + t • v) t := by
  fun_prop

/-! ## The finite Fourier formula for the coefficients -/

/-- Grid points `(ω^{kᵢ})ᵢ` of the finite Fourier average of order `n`. -/
def polydiscGridPoint (n : ℕ) (k : Fin d → Fin (n + 1)) : Fin d → ℂ :=
  fun i => polydiscRoot n ^ (k i : ℕ)

/-- Conjugate characters `∏ᵢ ω^{kᵢ (n+1-αᵢ)}` of the finite Fourier average. -/
def polydiscGridWeight (n : ℕ) (α : Fin d → ℕ) (k : Fin d → Fin (n + 1)) : ℂ :=
  ∏ i, polydiscRoot n ^ ((k i : ℕ) * (n + 1 - α i))

theorem norm_polydiscGridPoint_le (n : ℕ) (k : Fin d → Fin (n + 1)) :
    ‖polydiscGridPoint n k‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
    simp only [polydiscGridPoint, norm_polydiscRoot_pow, le_refl]

/-- **Fourier formula.** Every canonical coefficient is a finite average of one-variable line
derivatives at `t = 0`. -/
theorem polydiscTaylorCoeff_eq_grid {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ}
    (hF : AnalyticAt ℂ F p₀) {n : ℕ} {α : Fin d → ℕ} (hn : ∑ i, α i = n) :
    polydiscTaylorCoeff F p₀ α =
      (((n + 1 : ℕ) : ℂ) ^ d)⁻¹ * (n.factorial : ℂ)⁻¹ *
        ∑ k : Fin d → Fin (n + 1),
          iteratedDeriv n (fun t : ℂ => F (p₀ + t • polydiscGridPoint n k)) 0 *
            polydiscGridWeight n α k := by
  have hα : α ∈ finiteCoordinateTaylorBox d n := mem_finiteCoordinateTaylorBox.mpr fun i => by
    rw [← hn]
    exact single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le (α j)) (mem_univ i)
  have h := sum_dft_coordinate_box (polydiscRoot_isPrimitiveRoot n)
    (fun β => if (∑ i, β i) = n then polydiscTaylorCoeff F p₀ β else 0) 1 hα
  simp only [one_mul, one_pow, mul_one, if_pos hn] at h
  have hQ : ∀ k : Fin d → Fin (n + 1),
      (∑ β ∈ finiteCoordinateTaylorBox d n,
          (if (∑ i, β i) = n then polydiscTaylorCoeff F p₀ β else 0) *
            ∏ i, (polydiscRoot n ^ (k i : ℕ)) ^ β i) =
        (n.factorial : ℂ)⁻¹ *
          iteratedDeriv n (fun t : ℂ => F (p₀ + t • polydiscGridPoint n k)) 0 := by
    intro k
    rw [← polydiscTaylorSeries_apply_diag_eq_line hF,
      polydiscTaylorSeries_apply_diag_eq_box]
    rfl
  simp_rw [hQ] at h
  have hne : ((n + 1 : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)
  have hC : polydiscTaylorCoeff F p₀ α = (((n + 1 : ℕ) : ℂ) ^ d)⁻¹ *
      (((n + 1 : ℕ) : ℂ) ^ d * polydiscTaylorCoeff F p₀ α) := by
    rw [inv_mul_cancel_left₀ hne]
  rw [hC, ← h, mul_assoc _ ((n.factorial : ℂ)⁻¹)]
  simp only [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [polydiscGridWeight]
  ring

/-! ## Cauchy estimates -/

/-- **Coefficient bound.** `‖C α‖ ≤ M (2/R)^{|α|}`. -/
theorem norm_polydiscTaylorCoeff_le {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ} {R M : ℝ}
    (hR : 0 < R) (hF : ∀ q ∈ ball p₀ R, AnalyticAt ℂ F q)
    (hM : ∀ q ∈ ball p₀ R, ‖F q‖ ≤ M) (α : Fin d → ℕ) :
    ‖polydiscTaylorCoeff F p₀ α‖ ≤ M * (2 / R) ^ (∑ i, α i) := by
  set n := ∑ i, α i with hn
  have hα : α ∈ finiteCoordinateTaylorBox d n := mem_finiteCoordinateTaylorBox.mpr fun i =>
    single_le_sum (fun j _ => Nat.zero_le (α j)) (mem_univ i)
  have hp₀ := hF p₀ (mem_ball_self hR)
  have hR2 : 0 ≤ R / 2 := by positivity
  have htorus := norm_coeff_mul_pow_le_of_torus
    (fun β => if (∑ i, β i) = n then polydiscTaylorCoeff F p₀ β else 0) hR2 hα
    (B := M) (fun x hx => ?_)
  · simp only [← hn, if_true] at htorus
    have hcancel : (R / 2) ^ n * (2 / R) ^ n = 1 := by
      rw [← mul_pow, show R / 2 * (2 / R) = 1 by field_simp, one_pow]
    calc ‖polydiscTaylorCoeff F p₀ α‖
        = ‖polydiscTaylorCoeff F p₀ α‖ * (R / 2) ^ n * (2 / R) ^ n := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ M * (2 / R) ^ n := mul_le_mul_of_nonneg_right htorus (by positivity)
  · have hxn : ‖x‖ ≤ R / 2 := (pi_norm_le_iff_of_nonneg hR2).mpr fun i => (hx i).le
    rw [← polydiscTaylorSeries_apply_diag_eq_box, polydiscTaylorSeries_apply_diag_eq_line hp₀]
    set g : ℂ → ℂ := fun t => F (p₀ + t • x)
    have hmem : ∀ t ∈ ball (0 : ℂ) 2, p₀ + t • x ∈ ball p₀ R := by
      intro t ht
      rw [mem_ball, dist_self_add_left, norm_smul]
      rw [mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖x‖ ≤ ‖t‖ * (R / 2) := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
        _ < 2 * (R / 2) := by gcongr
        _ = R := by ring
    have hg : DifferentiableOn ℂ g (ball 0 2) := fun t ht =>
      ((hF _ (hmem t ht)).differentiableAt.comp t
        (differentiableAt_line p₀ x t)).differentiableWithinAt
    have hc := norm_iteratedDeriv_le_of_ball n two_pos hg (fun t ht => hM _ (hmem t ht))
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n g 0‖
        ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * M / (2 / 2) ^ n) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = M := by
          rw [show (2 : ℝ) / 2 = 1 by norm_num, one_pow, div_one, inv_mul_cancel_left₀ hfac.ne']

/-- The constant of the box remainder bound. -/
def polydiscRemainderConst (d N : ℕ) : ℝ :=
  (N + 1).factorial * 4 ^ (N + 1) + ((N + 1) ^ d : ℕ) * 2 ^ (N + 1)

theorem polydiscRemainderConst_nonneg (d N : ℕ) : 0 ≤ polydiscRemainderConst d N := by
  unfold polydiscRemainderConst
  positivity

/-- The one-variable Taylor polynomial of the line restriction is the total-degree Taylor
polynomial. -/
theorem polydiscTaylorSeries_partialSum_eq_line {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ}
    (hF : AnalyticAt ℂ F p₀) (N : ℕ) (x : Fin d → ℂ) :
    (polydiscTaylorSeries F p₀).partialSum (N + 1) x =
      complexTaylorSum (fun t : ℂ => F (p₀ + t • x)) (N + 1) 0 1 := by
  unfold FormalMultilinearSeries.partialSum complexTaylorSum
  refine sum_congr rfl fun m _ => ?_
  rw [polydiscTaylorSeries_apply_diag_eq_line hF]
  simp

/-- The line Taylor remainder: `‖F(p₀ + x) - T_N(x)‖ ≤ (N+1)! 4^{N+1} M (‖x‖/R)^{N+1}`. -/
theorem norm_sub_line_taylor_le {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ} {R M : ℝ}
    (hR : 0 < R) (hF : ∀ q ∈ ball p₀ R, AnalyticAt ℂ F q)
    (hM : ∀ q ∈ ball p₀ R, ‖F q‖ ≤ M) (N : ℕ) {x : Fin d → ℂ} (hx : ‖x‖ ≤ R / 4) :
    ‖F (p₀ + x) - complexTaylorSum (fun t : ℂ => F (p₀ + t • x)) (N + 1) 0 1‖ ≤
      (N + 1).factorial * 4 ^ (N + 1) * M * (‖x‖ / R) ^ (N + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀ (mem_ball_self hR))
  by_cases hx0 : x = 0
  · subst hx0
    have hconst : (fun t : ℂ => F (p₀ + t • (0 : Fin d → ℂ))) = fun _ => F p₀ := by
      funext t
      simp
    rw [hconst]
    have hT : complexTaylorSum (fun _ : ℂ => F p₀) (N + 1) 0 1 = F p₀ := by
      unfold complexTaylorSum
      rw [sum_range_succ']
      simp [iteratedDeriv_const]
    rw [hT, add_zero, sub_self, norm_zero]
    positivity
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set ρ := R / ‖x‖ with hρ
    have hρpos : 0 < ρ := div_pos hR hxpos
    have hρ4 : 4 ≤ ρ := by
      rw [hρ, le_div_iff₀ hxpos]
      linarith
    have hmem : ∀ t ∈ ball (0 : ℂ) ρ, p₀ + t • x ∈ ball p₀ R := by
      intro t ht
      rw [mem_ball, dist_self_add_left, norm_smul]
      rw [mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖x‖ < ρ * ‖x‖ := mul_lt_mul_of_pos_right ht hxpos
        _ = R := by rw [hρ]; field_simp
    have hg : DifferentiableOn ℂ (fun t : ℂ => F (p₀ + t • x)) (ball 0 ρ) := fun t ht =>
      ((hF _ (hmem t ht)).differentiableAt.comp t
        (differentiableAt_line p₀ x t)).differentiableWithinAt
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (ρ / 2) := by
      rw [mem_ball, dist_zero_right, norm_one]
      linarith
    have ht := norm_sub_complexTaylorSum_le_of_ball (N + 1) hρpos hg
      (fun t ht => hM _ (hmem t ht)) h1
    simp only [one_smul, sub_zero, norm_one, one_pow, mul_one] at ht
    refine ht.trans (le_of_eq ?_)
    have hinv : (ρ / 4)⁻¹ = 4 * (‖x‖ / R) := by
      rw [hρ]
      field_simp
    rw [div_eq_mul_inv _ ((ρ / 4) ^ (N + 1)), ← inv_pow, hinv, mul_pow]
    ring

/-- **Box remainder.** For `‖x‖ ≤ R/4`,
`‖F(p₀ + x) - ∑_{α ∈ box N} C α x^α‖ ≤ K(d,N) M (‖x‖/R)^{N+1}`. -/
theorem norm_sub_polydiscTaylorBox_le {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ} {R M : ℝ}
    (hR : 0 < R) (hF : ∀ q ∈ ball p₀ R, AnalyticAt ℂ F q)
    (hM : ∀ q ∈ ball p₀ R, ‖F q‖ ≤ M) (N : ℕ) {x : Fin d → ℂ} (hx : ‖x‖ ≤ R / 4) :
    ‖F (p₀ + x) - ∑ α ∈ finiteCoordinateTaylorBox d N,
        polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i‖ ≤
      polydiscRemainderConst d N * M * (‖x‖ / R) ^ (N + 1) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀ (mem_ball_self hR))
  have hp₀ := hF p₀ (mem_ball_self hR)
  set P := polydiscTaylorSeries F p₀
  set S := ∑ α ∈ finiteCoordinateTaylorBox d N, polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i
  set T := P.partialSum (N + 1) x
  have hline := norm_sub_line_taylor_le hR hF hM N hx
  rw [← polydiscTaylorSeries_partialSum_eq_line hp₀] at hline
  have hST : S - T = ∑ α ∈ finiteCoordinateTaylorBox d N,
      if (∑ i, α i) ≤ N then 0 else polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i := by
    simp only [S, T, P, partialSum_eq_coordinate_box_total_degree, ← sum_sub_distrib]
    refine sum_congr rfl fun α _ => ?_
    split_ifs <;> simp [polydiscTaylorCoeff]
  have hxR : 0 ≤ 2 * ‖x‖ / R := by positivity
  have hxR1 : 2 * ‖x‖ / R ≤ 1 := by
    rw [div_le_one hR]
    linarith
  have hterm : ∀ α ∈ finiteCoordinateTaylorBox d N,
      ‖if (∑ i, α i) ≤ N then (0 : ℂ) else polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i‖ ≤
        M * 2 ^ (N + 1) * (‖x‖ / R) ^ (N + 1) := by
    intro α _
    split_ifs with hα
    · rw [norm_zero]
      positivity
    · push Not at hα
      have hmono : ‖∏ i, x i ^ α i‖ ≤ ‖x‖ ^ (∑ i, α i) := by
        rw [norm_prod, ← prod_pow_eq_pow_sum]
        refine prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) _
      calc ‖polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i‖
          ≤ M * (2 / R) ^ (∑ i, α i) * ‖x‖ ^ (∑ i, α i) := by
            rw [norm_mul]
            exact mul_le_mul (norm_polydiscTaylorCoeff_le hR hF hM α) hmono (norm_nonneg _)
              (by positivity)
        _ = M * (2 * ‖x‖ / R) ^ (∑ i, α i) := by
            rw [mul_assoc, ← mul_pow]
            congr 2
            ring
        _ ≤ M * (2 * ‖x‖ / R) ^ (N + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hxR hxR1 hα) hM0
        _ = M * 2 ^ (N + 1) * (‖x‖ / R) ^ (N + 1) := by
            rw [mul_assoc, ← mul_pow]
            congr 2
            ring
  have hsum : ‖S - T‖ ≤ ((N + 1) ^ d : ℕ) * 2 ^ (N + 1) * M * (‖x‖ / R) ^ (N + 1) := by
    rw [hST]
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
    rw [sum_const, nsmul_eq_mul]
    simp only [finiteCoordinateTaylorBox, Fintype.card_piFinset, card_range, prod_const,
      card_univ, Fintype.card_fin]
    push_cast
    ring
  have htri : ‖F (p₀ + x) - S‖ ≤ ‖F (p₀ + x) - T‖ + ‖S - T‖ := by
    have : F (p₀ + x) - S = (F (p₀ + x) - T) - (S - T) := by ring
    rw [this]
    exact norm_sub_le _ _
  refine htri.trans ((add_le_add hline hsum).trans (le_of_eq ?_))
  unfold polydiscRemainderConst
  ring

/-- The box remainder in terms of the coordinate norm sum `∑ᵢ ‖xᵢ‖`. -/
theorem norm_sub_polydiscTaylorBox_le_sum {F : (Fin d → ℂ) → ℂ} {p₀ : Fin d → ℂ} {R M : ℝ}
    (hR : 0 < R) (hF : ∀ q ∈ ball p₀ R, AnalyticAt ℂ F q)
    (hM : ∀ q ∈ ball p₀ R, ‖F q‖ ≤ M) (N : ℕ) {x : Fin d → ℂ} (hx : ‖x‖ ≤ R / 4) :
    ‖F (p₀ + x) - ∑ α ∈ finiteCoordinateTaylorBox d N,
        polydiscTaylorCoeff F p₀ α * ∏ i, x i ^ α i‖ ≤
      polydiscRemainderConst d N * M * ((∑ i, ‖x i‖) / R) ^ (N + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀ (mem_ball_self hR))
  have hs : 0 ≤ ∑ i, ‖x i‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hnorm : ‖x‖ ≤ ∑ i, ‖x i‖ := (pi_norm_le_iff_of_nonneg hs).mpr fun i =>
    single_le_sum (fun j _ => norm_nonneg (x j)) (mem_univ i)
  refine (norm_sub_polydiscTaylorBox_le hR hF hM N hx).trans ?_
  have := polydiscRemainderConst_nonneg d N
  gcongr

end PGM
