import PLAStochastic.Index.CEPS.Canonical.Domain

/-!
# CEPS WP3: existence of canonical-factor domain constants

`cepsCanonDomain_exists`: for every step class `(D, θ, v)` with `D, θ, v > 0` there is a
`CepsCanonDomain D θ v`. The constants are explicit (successive minima), chosen in the order
`ρA, ρB → gF, g → c₀, η → rmax → μ₀, q₀` (blueprint §3.0: the drift and discount radii are small
compared with the line abscissa, which is small compared with the root zone).
-/

noncomputable section

namespace PGM

theorem mul_le_of_le_div' {x a b : ℝ} (hb : 0 < b) (h : x ≤ a / b) : b * x ≤ a := by
  rw [le_div_iff₀ hb] at h; linarith

/-- **Domain constants exist** for every class `(D, θ, v)`. -/
theorem cepsCanonDomain_exists {D θ v : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hv : 0 < v) :
    Nonempty (CepsCanonDomain D θ v) := by
  set R := cepsChartRadius D θ with hR
  set C3 := cepsCgfC3 D θ with hC3
  set vl := cepsVarLo D with hvl
  set r0 := cepsCgfRadius D θ with hr0
  set K := cepsChartK D with hK
  set r1 := cepsChartRho D θ with hr1
  set μc := cepsChartMu D θ with hμc
  set CW := cepsShiftConst D θ with hCW
  have pR : 0 < R := cepsChartRadius_pos hD hθ
  have pC3 : 0 < C3 := cepsCgfC3_pos hD hθ
  have pvl : 0 < vl := cepsVarLo_pos hD
  have pr0 : 0 < r0 := cepsCgfRadius_pos hD hθ
  have pK : 0 < K := cepsChartK_pos hD
  have pr1 : 0 < r1 := cepsChartRho_pos hD hθ
  have pμc : 0 < μc := cepsChartMu_pos hD hθ
  have pCW : 0 < CW := cepsShiftConst_pos hD hθ
  have hRr0 : R ≤ r0 / 8 := cepsChartRadius_le_r0
  -- `ρA`
  set ρA := min (min (R / 4) (vl / (1920 * C3))) (min 1 (vl / (144 * v ^ 2))) with hρA
  have pρA : 0 < ρA := lt_min (lt_min (by positivity) (by positivity))
    (lt_min one_pos (by positivity))
  have ρA1 : ρA ≤ R / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have ρA2 : ρA ≤ vl / (1920 * C3) := (min_le_left _ _).trans (min_le_right _ _)
  have ρA3 : ρA ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have ρA4 : ρA ≤ vl / (144 * v ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- `ρB`
  set ρB := min (r0 / 4) (vl / (32 * C3)) with hρB
  have pρB : 0 < ρB := lt_min (by positivity) (by positivity)
  have ρB1 : ρB ≤ r0 / 4 := min_le_left _ _
  have ρB2 : ρB ≤ vl / (32 * C3) := min_le_right _ _
  have ρAB : ρA ≤ ρB := by
    refine le_min (by linarith) (ρA2.trans ?_)
    exact div_le_div_of_nonneg_left pvl.le (by positivity) (by linarith)
  -- gaps
  set gF := min (cepsGap D v (ρB / 2)) (1 / 2) with hgF
  have pgF : 0 < gF := lt_min (cepsGap_pos hD hv (by positivity)) (by norm_num)
  have gF1 : gF ≤ cepsGap D v (ρB / 2) := min_le_left _ _
  have gF2 : gF ≤ 1 / 2 := min_le_right _ _
  set g := min (1 - Real.exp (-(vl * ρA ^ 2 / 16))) (gF / 2) with hg
  have pg : 0 < g := by
    refine lt_min ?_ (by positivity)
    have : Real.exp (-(vl * ρA ^ 2 / 16)) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < vl * ρA ^ 2 / 16 := by positivity
      linarith)
    linarith
  have g1 : g ≤ 1 - Real.exp (-(vl * ρA ^ 2 / 16)) := min_le_left _ _
  have g2 : g ≤ gF / 2 := min_le_right _ _
  -- `c₀`, `η`
  set c₀ := min (ρA * g / 1000) (gF / (8 * CW)) with hc₀
  have pc₀ : 0 < c₀ := lt_min (by positivity) (by positivity)
  have c1 : c₀ ≤ ρA * g / 1000 := min_le_left _ _
  have c2 : c₀ ≤ gF / (8 * CW) := min_le_right _ _
  set η := gF / 32 with hη
  -- `rmax`
  set rmax := min (min (min (r1 / 2) (c₀ / (8 * K))) (min (ρA * vl / 192) ρA))
    (min (min (ρA * vl / (576 * v * K)) (vl / (64 * v)))
      (min (min 1 (vl * ρA / 16)) (gF / 16))) with hrmax
  have prmax : 0 < rmax := by
    refine lt_min (lt_min (lt_min ?_ ?_) (lt_min ?_ pρA)) (lt_min (lt_min ?_ ?_)
      (lt_min (lt_min one_pos ?_) ?_)) <;> positivity
  have r1' : rmax ≤ r1 / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have r2' : rmax ≤ c₀ / (8 * K) :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have r3' : rmax ≤ ρA * vl / 192 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have r4' : rmax ≤ ρA := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have r5' : rmax ≤ ρA * vl / (576 * v * K) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have r6' : rmax ≤ vl / (64 * v) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have r7' : rmax ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _)))
  have r8' : rmax ≤ vl * ρA / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _)))
  have r9' : rmax ≤ gF / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- `μ₀`
  set μ₀ := min (min (vl * rmax / (4 * (v + 1))) (vl * c₀ / 16))
    (min (vl * ρA ^ 2 / (64 * ρB)) (min (gF / 64) (μc / 2))) with hμ₀
  have pμ₀ : 0 < μ₀ := by
    refine lt_min (lt_min ?_ ?_) (lt_min ?_ (lt_min ?_ ?_)) <;> positivity
  have m1 : μ₀ ≤ vl * rmax / (4 * (v + 1)) := (min_le_left _ _).trans (min_le_left _ _)
  have m2 : μ₀ ≤ vl * c₀ / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have m3 : μ₀ ≤ vl * ρA ^ 2 / (64 * ρB) := (min_le_right _ _).trans (min_le_left _ _)
  have m4 : μ₀ ≤ gF / 64 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have m5 : μ₀ ≤ μc / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨{
    ρA := ρA, ρB := ρB, gF := gF, g := g, c₀ := c₀, μ₀ := μ₀, q₀ := rmax ^ 2 / 2, η := η,
    rmax := rmax
    ρA_pos := pρA
    ρA_R := by linarith
    ρA_C3 := by have := mul_le_of_le_div' (by positivity) ρA2; linarith
    ρA_one := ρA3
    ρA_v := mul_le_of_le_div' (by positivity) ρA4
    ρA_ρB := ρAB
    ρB_r0 := by linarith
    ρB_C3 := by have := mul_le_of_le_div' (by positivity) ρB2; linarith
    gF_pos := pgF
    gF_le := gF2
    gF_gap := gF1
    g_pos := pg
    g_gF := g2
    g_B := g1
    c₀_pos := pc₀
    c₀_g := by linarith
    c₀_W := by have := mul_le_of_le_div' (by positivity) c2; linarith
    η_pos := by positivity
    η_le := by rw [hη]; linarith
    rmax_pos := prmax
    rmax_r1 := by linarith
    rmax_c₀ := by have := mul_le_of_le_div' (by positivity) r2'; linarith
    rmax_A1 := by linarith
    rmax_A1' := r4'
    rmax_A2 := by have := mul_le_of_le_div' (by positivity) r5'; linarith
    rmax_A3 := by have := mul_le_of_le_div' (by positivity) r6'; linarith
    rmax_one := r7'
    rmax_B := by linarith
    rmax_C := by linarith
    μ₀_pos := pμ₀
    μ₀_r := by have := mul_le_of_le_div' (by positivity) m1; linarith
    μ₀_c₀ := by linarith
    μ₀_B := by have := mul_le_of_le_div' (by positivity) m3; linarith
    μ₀_C := by linarith
    μ₀_chart := by linarith
    q₀_def := rfl }⟩

end PGM
