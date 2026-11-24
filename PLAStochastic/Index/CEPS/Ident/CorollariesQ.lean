import PLAStochastic.Index.CEPS.Ident.Statement

/-!
# CEPS C-6, preliminaries: the quotient `Q` and the regularity of `L` in `ζ`

Facts about the frozen objects of `Ident.Statement` that do not use the identification:

* `CepsC6.dslope_eq_of_eqOn_mul`: if `f = (· - a) g` on an open set `U ∋ a` and `g` is
  differentiable at `a`, then `dslope f a = g` on `U`;
* `CepsC6.cepsQ_eq_cepsQuotA`: on `ball 0 ρA`, `Q = cepsQ` coincides with the zone-A quotient
  `Q_A`; hence `Q ≠ 0` and `Q` is holomorphic there;
* `CepsC6.cepsD_eq_mul_cepsQ`: `d(ζ) = (β₊ - ζ)(ζ - β₋) Q(ζ)` for every `ζ` (blueprint (3.2));
* `CepsC6.cepsQ_ne_zero`: `Q ≠ 0` on the strip `|Re ζ| ≤ 2 c₀` (real drift);
* `CepsC6.cepsQ_rootPlus_mul`, `cepsQ_rootMinus_mul`: `Q(β₊)(β₊ - β₋) = ψ_μ'(β₊)` and
  `Q(β₋)(β₊ - β₋) = -ψ_μ'(β₋)`;
* `CepsC6.differentiableAt_canonL`: `ζ ↦ L(ζ)` is holomorphic on `Re ζ < c₀` for every
  `‖q‖ ≤ q₀` (closed disc);
* `CepsC6.μ₀_le`: `μ₀ ≤ 1/(64 D)` (the small-drift threshold of the W library).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

namespace CepsC6

/-- If `f = (· - a) g` on an open neighbourhood `U` of `a` and `g` is differentiable at `a`,
then `dslope f a = g` on `U`. -/
theorem dslope_eq_of_eqOn_mul {f g : ℂ → ℂ} {a : ℂ} {U : Set ℂ} (hU : IsOpen U) (ha : a ∈ U)
    (hfg : ∀ z ∈ U, f z = (z - a) * g z) (hg : DifferentiableAt ℂ g a) {z : ℂ} (hz : z ∈ U) :
    dslope f a z = g z := by
  by_cases h : z = a
  · subst h
    rw [dslope_same]
    have hd : HasDerivAt (fun w => (w - z) * g w) (1 * g z + (z - z) * deriv g z) z :=
      ((hasDerivAt_id' z).sub_const z).mul hg.hasDerivAt
    have he : f =ᶠ[𝓝 z] fun w => (w - z) * g w :=
      Filter.eventually_of_mem (hU.mem_nhds ha) hfg
    rw [(hd.congr_of_eventuallyEq he).deriv]
    ring
  · rw [dslope_of_ne _ h, slope_def_field, hfg z hz, hfg a ha, sub_self, zero_mul, sub_zero,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr h)]

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hW in
theorem ρA_lt_cgfRadius : dom.ρA < cepsCgfRadius D θ := by
  have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have := cepsCgfRadius_pos hD hθ; have := dom.ρA_pos; linarith

theorem rootPlus_mem_ball {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    cepsRootPlus D θ ρW μ q ∈ ball (0 : ℂ) dom.c₀ := by
  have := dom.norm_rootPlus_le hW hθ hD hμ hq; have := dom.c₀_pos
  exact mem_ball_zero_iff.mpr (by linarith)

theorem rootMinus_mem_ball {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    cepsRootMinus D θ ρW μ q ∈ ball (0 : ℂ) dom.c₀ := by
  have := dom.norm_rootMinus_le hW hθ hD hμ hq; have := dom.c₀_pos
  exact mem_ball_zero_iff.mpr (by linarith)

omit hW hθ hD in
theorem ball_c₀_subset : ball (0 : ℂ) dom.c₀ ⊆ ball (0 : ℂ) dom.ρA := by
  have := dom.c₀_le; have := dom.c₀_pos; have := dom.ρA_pos
  exact ball_subset_ball (by linarith)

theorem differentiableAt_cepsQuotA {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) dom.ρA) : DifferentiableAt ℂ (cepsQuotA D θ ρW μ q) w := by
  have hw' : w ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
    ball_subset_ball (ρA_lt_cgfRadius dom hθ hD).le hw
  exact (dom.differentiableOn_cepsQuotA hW hθ hD hμ hq w hw').differentiableAt
    (isOpen_ball.mem_nhds hw')

/-- `-d = (ζ - β₊)(ζ - β₋) Q_A` on `ball 0 ρA`. -/
theorem negD_eq_zoneA {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) dom.ρA) :
    -cepsD ρW μ q w = (w - cepsRootPlus D θ ρW μ q) *
      ((w - cepsRootMinus D θ ρW μ q) * cepsQuotA D θ ρW μ q w) := by
  rw [dom.cepsD_eq_zoneA hW hθ hD hμ hq (mem_ball_zero_iff.mp hw).le, cepsQuad]; ring

/-- `dslope (-d) β₊ = (· - β₋) Q_A` on `ball 0 ρA`. -/
theorem dslope_negD_eq {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) dom.ρA) :
    dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q) w =
      (w - cepsRootMinus D θ ρW μ q) * cepsQuotA D θ ρW μ q w := by
  have hbp := ball_c₀_subset dom (rootPlus_mem_ball dom hW hθ hD hμ hq)
  refine dslope_eq_of_eqOn_mul (f := fun z => -cepsD ρW μ q z)
    (g := fun z => (z - cepsRootMinus D θ ρW μ q) * cepsQuotA D θ ρW μ q z) isOpen_ball hbp
    (fun z hz => negD_eq_zoneA dom hW hθ hD hμ hq hz) ?_ hw
  exact (by fun_prop : DifferentiableAt ℂ (fun z => z - cepsRootMinus D θ ρW μ q) _).mul
    (differentiableAt_cepsQuotA dom hW hθ hD hμ hq hbp)

/-- **`Q = Q_A` on the root zone.** -/
theorem cepsQ_eq_cepsQuotA {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) dom.ρA) : cepsQ D θ ρW μ q z = cepsQuotA D θ ρW μ q z := by
  have hbm := ball_c₀_subset dom (rootMinus_mem_ball dom hW hθ hD hμ hq)
  exact dslope_eq_of_eqOn_mul isOpen_ball hbm
    (fun w hw => dslope_negD_eq dom hW hθ hD hμ hq hw)
    (differentiableAt_cepsQuotA dom hW hθ hD hμ hq hbm) hz

theorem cepsQ_ne_zero_of_mem_ball {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) dom.ρA) : cepsQ D θ ρW μ q z ≠ 0 := by
  rw [cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq hz]
  exact dom.cepsQuotA_ne_zero hW hθ hD hμ hq (mem_ball_zero_iff.mp hz).le

theorem differentiableAt_cepsQ {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) dom.ρA) : DifferentiableAt ℂ (cepsQ D θ ρW μ q) z := by
  refine (differentiableAt_cepsQuotA dom hW hθ hD hμ hq hz).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq hw

/-- **Blueprint (3.2).** `d(ζ) = (β₊ - ζ)(ζ - β₋) Q(ζ)` for every `ζ`. -/
theorem cepsD_eq_mul_cepsQ {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) (z : ℂ) :
    cepsD ρW μ q z = (cepsRootPlus D θ ρW μ q - z) * (z - cepsRootMinus D θ ρW μ q) *
      cepsQ D θ ρW μ q z := by
  set bp := cepsRootPlus D θ ρW μ q
  set bm := cepsRootMinus D θ ρW μ q
  set f : ℂ → ℂ := fun z => -cepsD ρW μ q z with hf
  have hbp := ball_c₀_subset dom (rootPlus_mem_ball dom hW hθ hD hμ hq)
  have hbm := ball_c₀_subset dom (rootMinus_mem_ball dom hW hθ hD hμ hq)
  have e1 := sub_smul_dslope f bp z
  have e2 := sub_smul_dslope (dslope f bp) bm z
  have h0 : f bp = 0 := by
    simp only [hf]; rw [negD_eq_zoneA dom hW hθ hD hμ hq hbp, sub_self, zero_mul]
  have h1 : dslope f bp bm = 0 := by
    rw [dslope_negD_eq dom hW hθ hD hμ hq hbm, sub_self, zero_mul]
  have hQ : cepsQ D θ ρW μ q z = dslope (dslope f bp) bm z := rfl
  rw [smul_eq_mul, h0, sub_zero] at e1
  rw [smul_eq_mul, h1, sub_zero] at e2
  rw [hQ]
  have : f z = -cepsD ρW μ q z := rfl
  linear_combination this + e1 + (z - bp) * e2

/-- `Q ≠ 0` on the strip `|Re ζ| ≤ 2 c₀` (real drift). -/
theorem cepsQ_ne_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {z : ℂ}
    (hz : |z.re| ≤ 2 * dom.c₀) : cepsQ D θ ρW μ q z ≠ 0 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  by_cases hr : z = cepsRootPlus D θ ρW μ q ∨ z = cepsRootMinus D θ ρW μ q
  · refine cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq ?_
    rcases hr with h | h <;> rw [h]
    · exact ball_c₀_subset dom (rootPlus_mem_ball dom hW hθ hD hμ' hq)
    · exact ball_c₀_subset dom (rootMinus_mem_ball dom hW hθ hD hμ' hq)
  · intro h0
    have hd : cepsD ρW μ q z = 0 := by
      rw [cepsD_eq_mul_cepsQ dom hW hθ hD hμ' hq z, h0, mul_zero]
    exact hr ((dom.cepsD_eq_zero_iff hW hθ hD hμ' (by simp; exact dom.η_pos.le) hq hz).mp hd)

/-- `-d` has derivative `ψ_μ'(b)` at a root `b` of `Φ = ψ_μ - q` near the origin. -/
theorem hasDerivAt_negD_of_root {μ q b : ℂ} (hb : ‖b‖ < cepsCgfRadius D θ)
    (hΦ : cepsRootEq ρW μ q b = 0) :
    HasDerivAt (fun z => -cepsD ρW μ q z) (deriv (cepsCgfShift ρW μ) b) b := by
  have hbB : b ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := mem_ball_zero_iff.mpr hb
  have hcgf := (differentiableOn_cepsCgf hW hθ hD b hbB).differentiableAt
    (isOpen_ball.mem_nhds hbB)
  have hψe : cepsCgfShift ρW μ = fun ζ => cepsCgf ρW ζ + μ * ζ := by
    funext ζ; rw [cepsCgfShift]
  have hψ : DifferentiableAt ℂ (cepsCgfShift ρW μ) b := by
    rw [hψe]; exact hcgf.add (differentiableAt_id.const_mul μ)
  have hΦd : HasDerivAt (cepsRootEq ρW μ q) (deriv (cepsCgfShift ρW μ) b) b := by
    have he : cepsRootEq ρW μ q = fun ζ => cepsCgfShift ρW μ ζ - q := by
      funext ζ; rw [cepsRootEq]
    rw [he]; exact hψ.hasDerivAt.sub_const q
  have hE : HasDerivAt (fun z => cexp (cepsRootEq ρW μ q z) - 1)
      (cexp (cepsRootEq ρW μ q b) * deriv (cepsCgfShift ρW μ) b) b :=
    hΦd.cexp.sub_const 1
  rw [hΦ, Complex.exp_zero, one_mul] at hE
  refine hE.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hbB] with z hz
  rw [CepsCanonDomain.cepsD_eq_one_sub_exp hW hθ hD (mem_ball_zero_iff.mp hz)]; ring

/-- `Q(β₊)(β₊ - β₋) = ψ_μ'(β₊)`. -/
theorem cepsQ_rootPlus_mul {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    cepsQ D θ ρW μ q (cepsRootPlus D θ ρW μ q) *
        (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) =
      deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q) := by
  set bp := cepsRootPlus D θ ρW μ q
  set bm := cepsRootMinus D θ ρW μ q
  have hbp := ball_c₀_subset dom (rootPlus_mem_ball dom hW hθ hD hμ hq)
  have hbr : ‖bp‖ < cepsCgfRadius D θ :=
    (mem_ball_zero_iff.mp hbp).trans (ρA_lt_cgfRadius dom hθ hD)
  have h1 := hasDerivAt_negD_of_root hW hθ hD hbr
    (cepsRootEq_rootPlus hW hθ hD (dom.μ_lt_chart hμ) (dom.norm_cepsRootR_lt hW hθ hD hμ hq))
  have hQd := (differentiableAt_cepsQ dom hW hθ hD hμ hq hbp).hasDerivAt
  have h2 : HasDerivAt (fun z => (z - bp) * ((z - bm) * cepsQ D θ ρW μ q z))
      (1 * ((bp - bm) * cepsQ D θ ρW μ q bp) +
        (bp - bp) * (1 * cepsQ D θ ρW μ q bp + (bp - bm) * deriv (cepsQ D θ ρW μ q) bp)) bp :=
    ((hasDerivAt_id' bp).sub_const bp).mul (((hasDerivAt_id' bp).sub_const bm).mul hQd)
  have he : (fun z => -cepsD ρW μ q z) = fun z => (z - bp) * ((z - bm) * cepsQ D θ ρW μ q z) := by
    funext z; rw [cepsD_eq_mul_cepsQ dom hW hθ hD hμ hq z]; ring
  rw [he] at h1
  have := h1.unique h2
  rw [this]; ring

/-- `Q(β₋)(β₊ - β₋) = -ψ_μ'(β₋)`. -/
theorem cepsQ_rootMinus_mul {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    cepsQ D θ ρW μ q (cepsRootMinus D θ ρW μ q) *
        (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) =
      -deriv (cepsCgfShift ρW μ) (cepsRootMinus D θ ρW μ q) := by
  set bp := cepsRootPlus D θ ρW μ q
  set bm := cepsRootMinus D θ ρW μ q
  have hbm := ball_c₀_subset dom (rootMinus_mem_ball dom hW hθ hD hμ hq)
  have hbr : ‖bm‖ < cepsCgfRadius D θ :=
    (mem_ball_zero_iff.mp hbm).trans (ρA_lt_cgfRadius dom hθ hD)
  have h1 := hasDerivAt_negD_of_root hW hθ hD hbr
    (cepsRootEq_rootMinus hW hθ hD (dom.μ_lt_chart hμ) (dom.norm_cepsRootR_lt hW hθ hD hμ hq))
  have hQd := (differentiableAt_cepsQ dom hW hθ hD hμ hq hbm).hasDerivAt
  have h2 : HasDerivAt (fun z => (z - bp) * ((z - bm) * cepsQ D θ ρW μ q z))
      (1 * ((bm - bm) * cepsQ D θ ρW μ q bm) +
        (bm - bp) * (1 * cepsQ D θ ρW μ q bm + (bm - bm) * deriv (cepsQ D θ ρW μ q) bm)) bm :=
    ((hasDerivAt_id' bm).sub_const bp).mul (((hasDerivAt_id' bm).sub_const bm).mul hQd)
  have he : (fun z => -cepsD ρW μ q z) = fun z => (z - bp) * ((z - bm) * cepsQ D θ ρW μ q z) := by
    funext z; rw [cepsD_eq_mul_cepsQ dom hW hθ hD hμ hq z]; ring
  rw [he] at h1
  have := h1.unique h2
  rw [this]; ring

/-- **Holomorphy of `L` in `ζ` on the closed `q`-disc.** -/
theorem differentiableAt_canonL {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ}
    (hζ : ζ.re < dom.c₀) : DifferentiableAt ℂ (dom.canonL ρW μ q) ζ := by
  have hc0 := dom.c₀_pos
  have hcle := dom.c₀_le
  have hρ1 := dom.ρA_one
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμi : (μ : ℂ).im = 0 := ofReal_im μ
  set G : ℝ → ℂ → ℂ := fun y _ =>
    Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q ((dom.c₀ : ℂ) + y * I)) with hG
  have hint : ∀ ζ' : ℂ, ζ'.re < dom.c₀ →
      Integrable (fun y : ℝ => ‖G y 0‖ / ‖(dom.c₀ : ℂ) + y * I - ζ'‖) := by
    intro ζ' h
    refine (dom.integrable_cepsCanonL_integrand hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith) hμ' hμi hq h).norm.congr ?_
    exact Filter.Eventually.of_forall fun y => by
      simp only [hG, cepsLineIntegrand, norm_div]
  have hm : ∀ q' ∈ ball (0 : ℂ) 1, AEStronglyMeasurable (fun y => G y q') volume :=
    fun _ _ => (dom.continuous_logF_line hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith) hμ' hμi hq).aestronglyMeasurable
  have hdiff := differentiableOn_lineIntegral_param (c := dom.c₀) (R := 1) (G := G)
    (B := fun y => ‖G y 0‖) (fun _ => differentiableOn_const _) (fun _ _ _ => le_rfl) hm hint
  have hmem : ((ζ, 0) : ℂ × ℂ) ∈ {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < 1} :=
    ⟨hζ, by simp⟩
  have hopen : IsOpen {x : ℂ × ℂ | x.1.re < dom.c₀ ∧ ‖x.2‖ < 1} :=
    (isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have h1 := (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
  have h2 := h1.comp ζ ((differentiableAt_id (𝕜 := ℂ) (x := ζ)).prodMk
    (differentiableAt_const (0 : ℂ)))
  have h3 : DifferentiableAt ℂ (fun ζ' : ℂ => Complex.log (((1 : ℝ) : ℂ) - ζ')) ζ := by
    refine ((differentiableAt_const _).sub differentiableAt_id).clog ?_
    have hre : 0 < (((1 : ℝ) : ℂ) - ζ).re := by
      rw [sub_re, ofReal_re]; linarith
    exact Or.inl hre
  exact (h2.const_mul ((2 * Real.pi : ℂ)⁻¹)).sub h3

omit hW hθ hD in
/-- Positivity of `1 - ζ` on `Re ζ < c₀`. -/
theorem one_sub_mem_slitPlane {ζ : ℂ} (hζ : ζ.re < dom.c₀) : (1 : ℂ) - ζ ∈ slitPlane := by
  have := dom.c₀_le; have := dom.ρA_one
  left; simp only [sub_re, one_re]; linarith

/-- **Small drift.** `μ₀ ≤ 1/(64 D)`. -/
theorem μ₀_le : dom.μ₀ ≤ 1 / (64 * D) := by
  have h1 := dom.μ₀_c₀
  have h2 := dom.c₀_le
  have h3 := dom.ρA_one
  have h4 := dom.ρA_v
  have h5 := CepsCanonDomain.varLo_le_v hW hθ hD
  have hρ := dom.ρA_pos
  have hc0 := dom.c₀_pos
  have hμ0 := dom.μ₀_pos
  set V := cepsVarLo D with hVdef
  have hV0 : 0 < V := cepsVarLo_pos hD
  have hVD : V * (256 * D ^ 2) = 1 := by rw [hVdef, cepsVarLo]; field_simp
  -- `ρA ≤ 64000 D`
  have hρD : dom.ρA ≤ 64000 * D := by
    rcases le_or_gt (1 / 64000) D with hDl | hDl
    · linarith
    · have hvV : V ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hV0.le h5 2
      have h6 : 144 * V ^ 2 * dom.ρA ≤ V := by nlinarith
      have h7 : 144 * V * dom.ρA ≤ 1 := by
        have : V * (144 * V * dom.ρA) ≤ V * 1 := by nlinarith
        exact le_of_mul_le_mul_left this hV0
      have h8 : dom.ρA = 256 * D ^ 2 * (V * dom.ρA) := by linear_combination -dom.ρA * hVD
      have h9 : 144 * dom.ρA ≤ 256 * D ^ 2 := by
        rw [h8]; nlinarith [sq_nonneg D]
      nlinarith
  -- `16000 μ₀ ≤ V ρA`
  have h10 : 16000 * dom.μ₀ ≤ V * dom.ρA := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  have h11 : dom.μ₀ * (64 * D) * 16000 ≤ 64 * D * (V * dom.ρA) := by nlinarith
  have h12 : 64 * D * (V * dom.ρA) ≤ 64 * D * (V * (64000 * D)) := by
    have : 0 ≤ 64 * D * V := by positivity
    nlinarith
  have h13 : 64 * D * (V * (64000 * D)) = 16000 := by linear_combination 16000 * hVD
  nlinarith

end CepsC6

end PGM
