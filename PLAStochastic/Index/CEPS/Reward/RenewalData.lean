import PLAStochastic.Index.CEPS.Reward.LadderDensity
import PLAStochastic.Index.CEPS.Scaled.RootBounds

/-! # Paying the exponential-renewal hypotheses for actual ladder densities

The smaller class domain keeps the actual root inside one quarter of the
closed renewal strip. All constants are selected before the step law.
-/

noncomputable section
open MeasureTheory Set Metric Complex
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

def renewalMu {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.μ₀ (dom.c₀ / (16 * dom.scaledRootDriftBound))

def renewalDiscount {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.q₀ ((dom.c₀ / (16 * cepsChartK D)) ^ 2)

def renewalLogBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀))

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem scaledRootDriftBound_pos : 0 < dom.scaledRootDriftBound := by
  have := cepsVarLo_pos hD
  have := cepsChartK_pos hD
  unfold scaledRootDriftBound
  positivity

include hD in
theorem renewalMu_pos : 0 < dom.renewalMu :=
  lt_min dom.μ₀_pos (div_pos dom.c₀_pos (mul_pos (by norm_num) (dom.scaledRootDriftBound_pos hD)))

include hD in
theorem renewalDiscount_pos : 0 < dom.renewalDiscount := by
  have := cepsChartK_pos hD
  exact lt_min dom.q₀_pos (sq_pos_of_pos (div_pos dom.c₀_pos
    (by positivity : 0 < 16 * cepsChartK D)))

include hW hθ hD in
theorem renewal_root_le {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq : ‖q‖ ≤ dom.renewalDiscount) :
    ‖cepsRootPlus D θ ρW μ q‖ ≤ (dom.c₀ / 2) / 4 := by
  have hm := hμ.trans (min_le_left _ _)
  have hq' := hq.trans (min_le_left _ _)
  have hp := (cepsRoots_norm_le_class dom hW hθ hD
    (by rwa [norm_real, Real.norm_eq_abs]) hq').1
  have hC := dom.scaledRootDriftBound_pos hD
  have hK := cepsChartK_pos hD
  have hc := dom.c₀_pos
  have hmd : dom.scaledRootDriftBound * |μ| ≤ dom.c₀ / 16 := by
    have := (le_div_iff₀ (by positivity : 0 < 16 * dom.scaledRootDriftBound)).mp
      (hμ.trans (min_le_right _ _))
    nlinarith
  have hqd : Real.sqrt ‖q‖ ≤ dom.c₀ / (16 * cepsChartK D) := by
    have ha : 0 ≤ dom.c₀ / (16 * cepsChartK D) := by positivity
    rw [← Real.sqrt_sq ha]
    exact Real.sqrt_le_sqrt (hq.trans (min_le_right _ _))
  have hkq : cepsChartK D * Real.sqrt ‖q‖ ≤ dom.c₀ / 16 := by
    have := (le_div_iff₀ (by positivity : 0 < 16 * cepsChartK D)).mp hqd
    nlinarith
  rw [norm_real, Real.norm_eq_abs] at hp
  linarith

include hW hθ hD in
/-- The actual complex ladder density meets every W-5 premise, uniformly in the class. -/
theorem actual_expRenewalData {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) :
    ExpRenewalData (cepsAscDensity ρW fW μ (cexp (-q))) dom.ladderEnvelope θ (dom.c₀ / 2)
      (cepsRootPlus D θ ρW μ q) (dom.canonL ρW μ q) dom.renewalLogBound := by
  have hm := hμ.trans (min_le_left _ _)
  have hq' := hq.trans (min_le_left _ _)
  have hs := norm_cexp_neg_le_one hq0
  have hc := dom.c₀_pos
  have ht := dom.two_c₀_lt
  refine ⟨cepsAscDensity_isExpDensity dom hW hθ hD hm hs, by positivity,
    by linarith, cepsAscDensity_weight_mass_lt dom hW hθ hD hm hs (by positivity),
    dom.renewal_root_le hW hθ hD hμ hq, ?_, ?_⟩
  · intro ζ hζ
    rw [cepsAscDensity_laplace_eq dom hW hθ hD hm hs
      (by have := le_of_abs_le hζ; linarith)]
    exact (dom.cepsWHIdent hW hθ hD μ hm q hq0 hq').1 ζ
      (by have := le_of_abs_le hζ; linarith)
  · intro ζ hζ
    have hne : 1 - ζ ≠ 0 := by
      intro he
      have hr := congrArg re he
      have h1 := dom.c₀_le
      have h2 := dom.ρA_one
      have h3 := le_of_abs_le hζ
      simp only [sub_re, one_re, zero_re] at hr
      linarith
    apply renewal_log_lower_of_norm_add_log hne
    exact dom.norm_cepsCanonL_add_log_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith) (by rwa [norm_real, Real.norm_eq_abs])
      (ofReal_im μ) hq' (le_of_abs_le hζ)

include hW hθ hD in
/-- Actual ascending renewal density with the canonical residue and explicit remainder. -/
theorem actual_renewalDensity_sub_le {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {x : ℝ} (hx : 0 < x) :
    ‖renewalDensity (cepsAscDensity ρW fW μ (cexp (-q))) x -
      cexp (-dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
        cexp (-cepsRootPlus D θ ρW μ q * x)‖ ≤
      (dom.ladderEnvelope + 2 * renewalFactorBound (dom.c₀ / 2) dom.renewalLogBound *
        dom.ladderEnvelope ^ 2 / ((dom.c₀ / 2) * (θ - (dom.c₀ / 2) / 2)) +
        7 * renewalFactorBound (dom.c₀ / 2) dom.renewalLogBound) *
          Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  have hr := dom.actual_expRenewalData hW hθ hD hμ hq0 hq
  have he := hr.renewalRes_eq_exp ((CepsC6.differentiableAt_canonL dom hW hθ hD
    (hμ.trans (min_le_left _ _)) (hq.trans (min_le_left _ _))
    (by have := re_le_norm (cepsRootPlus D θ ρW μ q)
        have := dom.renewal_root_le hW hθ hD hμ hq; linarith [dom.c₀_pos])).continuousAt)
  simpa only [he] using hr.norm_renewalDensity_sub_le hx

end PGM.CepsCanonDomain
