import PLAStochastic.Index.KRE.Uniform.Main
import PLAStochastic.Index.KRE.Exact.LayerRules
import PLAStochastic.Index.KRE.Exact.Deterministic
import PLAStochastic.Index.KRE.Exact.Numeric

/-!
# K-RE exact: the fixed-density integer height off both jump windows

The noise phase doubles the logarithmic spacing. The curvature phase
halves the logarithmic size, with bounded accumulated error. HEIGHT and
the two window exclusions select the exact integers in these phases.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
universe u

/-- The exact formula holds uniformly for the full-curvature members
`d.Mem 1 f`, on the canonical good event. -/
theorem K_RE_exact_class (d : DensityClassParams) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ f, d.Mem 1 f → ∀ ω : ℕ → ℝ,
        ω ∉ kreBad expCoord (N k) (ε k) (tRE (N k)) (jK (N k)) →
        KREOutside (kreZ (N k) (ε k)) (greW K (N k) (ε k)) →
        reHeight (ε k) (renyiKeys f (N k) ω) (N k) = kreExactHeight (kreZ (N k) (ε k)) := by
  obtain ⟨cN, CN, Cu, C0, c1, c2, c3, KL, hcN, hCN, hCu, hC0, hc1, hc2, hc3, hKL, hlay⟩ :=
    uniformLayerFacts_of_good d
  let c := min c1 (min c2 c3)
  have hc : 0 < c := lt_min hc1 (lt_min hc2 hc3)
  have h1 : c ≤ c1 := min_le_left _ _
  have h2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : c ≤ c3 := (min_le_right _ _).trans (min_le_right _ _)
  let G := 2 * (Cu + C0)
  let C := 1 + KL + 16 / c ^ 2
  have hCp : 0 < C := by dsimp [C]; positivity
  have hC : 1 ≤ C := by dsimp [C]; have := div_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg c); linarith
  have hCc : 16 ≤ c ^ 2 * C := by
    have heq : c ^ 2 * (16 / c ^ 2) = 16 := by field_simp [hc.ne']
    dsimp [C]
    nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) hKL.le]
  have hCK : KL ≤ C := by dsimp [C]; have := div_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg c); linarith
  let A := 1 + |Real.log cN| + |Real.log CN| + |Real.log (c / 2)| +
    |Real.log G| + |Real.log C| + |Real.log (1 + 24 * unifKappa d)|
  have hall : 1 ≤ A ∧ |Real.log cN| ≤ A ∧ |Real.log CN| ≤ A ∧
      |Real.log (c / 2)| ≤ A ∧ |Real.log G| ≤ A ∧ |Real.log C| ≤ A ∧
      |Real.log (1 + 24 * unifKappa d)| ≤ A := by
    dsimp [A]
    repeat' constructor
    all_goals linarith [abs_nonneg (Real.log cN), abs_nonneg (Real.log CN),
      abs_nonneg (Real.log (c / 2)), abs_nonneg (Real.log G), abs_nonneg (Real.log C),
      abs_nonneg (Real.log (1 + 24 * unifKappa d))]
  obtain ⟨hA, hAN, hAN', hAc, hAG, hAC, hAB⟩ := hall
  have hAp : 0 < A := by linarith
  have hAl : -A ≤ Real.log (c / 2) := (neg_le_neg hAc).trans (neg_abs_le _)
  have hAu : Real.log G ≤ A := (le_abs_self _).trans hAG
  have hlo : -A ≤ Real.log cN := (neg_le_neg hAN).trans (neg_abs_le _)
  have hhi : Real.log CN ≤ A := (le_abs_self _).trans hAN'
  refine ⟨1000 * A, by positivity, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [hlay hN hε hεN, eventually_unifCond d hN hε,
    eventually_KRENumeric hA hN hε hεN] with k hL hd hp
  intro f hf ω hω hwin
  have hF := hL ω hω 1 f hf
  obtain ⟨hstep, hstop⟩ := kre_exact_layer_rules hf hd hω hF hp.big hp.growth hc h1 h2 h3
    hCu hC0 (le_rfl : 2 * (Cu + C0) ≤ G) hC hCc hCK hAl hAu
    ((le_abs_self _).trans hAC) ((le_abs_self _).trans hAB)
  have he := hp.eps_one
  have hw : 0 < greW (1000 * A) (N k) (ε k) := by
    have he' := Real.log_pos he
    have hY' : 0 < Real.log (N k) := by linarith [hp.log_n_one]
    have hlogY := Real.log_nonneg hp.log_n_one
    unfold greW
    positivity
  exact kre_exact_from_layers hF he.le hp.n_two hp.log_n_one hcN hCN (by linarith)
    hp.rho hlo hhi hp.q_one (kre_q_identity he) hw hp.window_one hwin hp.margin hp.separation
    (by linarith [Real.log_pos he]) hstep hstop

/-- Every fixed nonconstant Model K density belongs to a full-curvature
class; endpoint nonconstancy gives an interior witness by continuity. -/
theorem exists_densityClass_mem {f : ℝ → ℝ} {fmin fmax Lf : ℝ}
    (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ d : DensityClassParams, d.Mem 1 f := by
  obtain ⟨a, b, ha, hab, hb, hne⟩ := exists_interior_ne hf hnc
  have hV : 0 < |f b - f a| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  let d : DensityClassParams :=
    { fmin := min fmin 1, fmax := max fmax 1, L := Lf + 1, V := |f b - f a|, a := a, b := b,
      fmin_pos := lt_min hf.pos one_pos, fmin_le_one := min_le_right _ _,
      one_le_fmax := le_max_right _ _, L_pos := by linarith [hf.lf_nonneg], V_pos := hV,
      a_pos := ha, a_lt_b := hab, b_lt_one := hb }
  refine ⟨d, zero_le_one, le_rfl, ?_, by simp [d]⟩
  exact
    { lt := hf.lt
      pos := lt_min hf.pos one_pos
      lower := fun x hx => (min_le_left _ _).trans (hf.lower x hx)
      upper := fun x hx => (hf.upper x hx).trans (le_max_left _ _)
      lip := fun x hx y hy => (hf.lip x hx y hy).trans (by
        show Lf * |x - y| ≤ 1 * (Lf + 1) * |x - y|
        nlinarith [abs_nonneg (x - y)])
      integral_one := hf.integral_one }

/-- `thm:KRE` (a): on an event of probability at least `1 - 63/N²`,
the actual RE height is the exact integer outside both jump windows. -/
theorem K_RE_exact {f : ℝ → ℝ} {fmin fmax Lf : ℝ} (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∃ E : Set (ℕ → ℝ), MeasurableSet E ∧
        expSeqMeasure.real Eᶜ ≤ 63 / (N k : ℝ) ^ 2 ∧
        ∀ ω ∈ E, KREOutside (kreZ (N k) (ε k)) (greW K (N k) (ε k)) →
          reHeight (ε k) (renyiKeys f (N k) ω) (N k) = kreExactHeight (kreZ (N k) (ε k)) := by
  obtain ⟨d, hd⟩ := exists_densityClass_mem hf hnc
  obtain ⟨K, hK, h⟩ := K_RE_exact_class d
  refine ⟨K, hK, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [h hN hε hεN, hN.eventually_ge_atTop 2,
    hε.eventually_ge_atTop (2 * epsZero 1 18)] with k hk hn he
  have hn1 : 1 ≤ N k := by exact_mod_cast (by linarith : (1 : ℝ) ≤ N k)
  refine ⟨(kreBad expCoord (N k) (ε k) (tRE (N k)) (jK (N k)))ᶜ,
    (measurableSet_kreBad measurable_expCoord _ _ _ _).compl, ?_, ?_⟩
  · rw [compl_compl]
    have hbad := measureReal_kreBad_le iidSeq_expCoord (hasLaw_expCoord 0) hn1
      (eps := ε k) (by linarith) (tRE (N k)) (jK (N k))
    exact hbad.trans (kreBadMass_le hn1)
  · intro ω hω hwin
    exact hk f hd ω (by simpa using hω) hwin

end
end PGM
