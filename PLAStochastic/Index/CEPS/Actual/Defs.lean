import PLAStochastic.Index.GEP.Kernel.Row.Measurable
import PLAStochastic.Index.GEP.RawDisc.ProductLaws

/-!
# P-CEPS WP8: actual strip objects of the exact marked representation

Objects of `research/2026-10-02-lean-ceps/blueprint-CS.md` §2.1 (theorem (E)), in drift units
`μ = 1/a - 1`, band width `l = w (1 + μ)`, discount `q`, and complex mark `t`.

* `CepsGapDensity ν f D`: `f` is a bounded density of `ν` vanishing on `(-∞, 0]`. Pointwise
  killed densities depend on the version `f`, so every density-valued object carries `f`.
* `cepsLaplace ν t = E e^{-tX}` (`φ(t)`).
* `cepsStripTerm ν t μ l n = E[e^{-t V_n}; V_0, …, V_n ∈ [0, l]]` for the outer walk
  `V_n = S_n - n (1 + μ)` (`kWalk 0 (-(1+μ)) (-1)`), and the entrance series
  `cepsStripEntrance ν t μ q l = ∑ₙ e^{-qn} cepsStripTerm ν t μ l n` (`H_t(μ, q, l)`).
* `cepsBridgeDens ν f μ l n = k_n^{(μ)}(0, l)`: the pointwise `n`-step density from `0` to `l` of
  the walk with step `Y_μ = 1 + μ - X` killed outside `[0, l]` (`krDens`).
* `cepsBridge` (`U = ∑_{n ≥ 1} e^{-qn} k_n`), `cepsMarkedBridge` (`𝔘 = ∑_{n ≥ 1} (n - w) e^{-qn} k_n`),
  and the actual pair `cepsActualPair ν f eps t μ = e^{tl} H_t² 𝔘` at `q = t(1+μ)`, `l = 2ε(1+μ)`.

Basic facts: word laws with equal letters are `iidLaw`, one-coordinate Fubini for integrable
complex integrands, and measurability of indicators of parameter-dependent bands.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-! ## Densities -/

/-- `f` is a bounded density of `ν` that vanishes on `(-∞, 0]`. -/
structure CepsGapDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (D : ℝ) : Prop where
  measurable : Measurable f
  nonneg : ∀ x, 0 ≤ f x
  le : ∀ x, f x ≤ D
  eq_zero : ∀ x, x ≤ 0 → f x = 0
  eq : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- A regular gap law has a bounded density vanishing on `(-∞, 0]`. -/
theorem RegLaw.exists_cepsGapDensity {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : RegLaw D θ vlo vhi ν) (hθ : 0 ≤ θ) : ∃ f, CepsGapDensity ν f D := by
  obtain ⟨f, hfm, hf0, hfz, hfD, hν⟩ := h.density
  have hD : 0 ≤ D := by
    have h1 := (hf0 1).trans (hfD 1)
    have h2 : 0 < Real.exp (-θ * 1) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left h1 h2
  refine ⟨f, hfm, hf0, fun x => ?_, hfz, hν⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [hfz x hx]; exact hD
  · refine (hfD x).trans ?_
    calc D * Real.exp (-θ * x) ≤ D * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith)) hD
      _ = D := mul_one D

namespace CepsGapDensity

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

theorem absolutelyContinuous (hf : CepsGapDensity ν f D) : (ν : Measure ℝ) ≪ volume := by
  rw [hf.eq]; exact withDensity_absolutelyContinuous _ _

theorem measure_Iic_zero (hf : CepsGapDensity ν f D) : (ν : Measure ℝ) (Iic 0) = 0 := by
  rw [hf.eq, withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic fun x hx => ?_).trans (lintegral_zero)
  simp [hf.eq_zero x hx]

theorem ae_pos (hf : CepsGapDensity ν f D) : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hf.measure_Iic_zero] with x hx
  simpa using hx

/-- Under `iidLaw ν` all gaps are a.s. positive. -/
theorem ae_iidLaw_pos (hf : CepsGapDensity ν f D) : ∀ᵐ g ∂(iidLaw ν), ∀ l, 0 < g l := by
  rw [ae_all_iff]
  intro l
  have hm := (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).measure_preimage
    (s := Iic 0) measurableSet_Iic.nullMeasurableSet
  rw [hf.measure_Iic_zero] at hm
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hm] with g hg
  simpa using hg

theorem nonneg_D (hf : CepsGapDensity ν f D) : 0 ≤ D := (hf.nonneg 0).trans (hf.le 0)

end CepsGapDensity

/-! ## Word laws with equal letters -/

theorem wordLaw_self (ν : ProbabilityMeasure ℝ) (S : Finset ℕ) : wordLaw ν ν S = iidLaw ν := by
  unfold wordLaw iidLaw
  simp only [ite_self]

theorem wordCoord_self (ν : ProbabilityMeasure ℝ) (S : Finset ℕ) (i : ℕ) :
    wordCoord ν ν S i = (ν : Measure ℝ) := by
  unfold wordCoord
  simp only [ite_self]

/-! ## One-coordinate Fubini for integrable complex integrands -/

/-- **One-coordinate Fubini** under `iidLaw ν` for an integrable complex integrand. -/
theorem integral_iidLaw_update (ν : ProbabilityMeasure ℝ) (m : ℕ) {F : (ℕ → ℝ) → ℂ}
    (hF : Integrable F (iidLaw ν)) :
    ∫ g, F g ∂(iidLaw ν) =
      ∫ g, ∫ x, F (Function.update g m x) ∂(ν : Measure ℝ) ∂(iidLaw ν) := by
  set ρ : ℕ → ProbabilityMeasure ℝ := fun _ => ν with hρ
  have hW : iidLaw ν = piLaw ρ := rfl
  have hmap := map_update_piLaw ρ m (ρ m)
  rw [Function.update_eq_self] at hmap
  have hU := measurable_update_pair m
  rw [hW]
  rw [hW, ← hmap] at hF
  have hint : Integrable (fun p : ℝ × (ℕ → ℝ) => F (Function.update p.2 m p.1))
      ((ρ m : Measure ℝ).prod (piLaw ρ)) :=
    (integrable_map_measure hF.aestronglyMeasurable hU.aemeasurable).1 hF
  calc ∫ g, F g ∂(piLaw ρ)
      = ∫ g, F g ∂(((ρ m : Measure ℝ).prod (piLaw ρ)).map
          (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 m p.1)) := by rw [hmap]
    _ = ∫ p, F (Function.update p.2 m p.1) ∂((ρ m : Measure ℝ).prod (piLaw ρ)) :=
        integral_map hU.aemeasurable hF.aestronglyMeasurable
    _ = ∫ g, ∫ x, F (Function.update g m x) ∂(ρ m : Measure ℝ) ∂(piLaw ρ) :=
        integral_prod_symm _ hint

/-! ## Indicators of parameter-dependent bands -/

theorem measurable_indicator_Icc_param {α : Type*} [MeasurableSpace α] {X lo hi : α → ℝ}
    (hX : Measurable X) (hlo : Measurable lo) (hhi : Measurable hi) :
    Measurable (fun p => (Icc (lo p) (hi p)).indicator (fun _ => (1 : ℝ)) (X p)) := by
  classical
  have hs : MeasurableSet {p | lo p ≤ X p ∧ X p ≤ hi p} :=
    (measurableSet_le hlo hX).inter (measurableSet_le hX hhi)
  have e : (fun p => (Icc (lo p) (hi p)).indicator (fun _ => (1 : ℝ)) (X p)) =
      {p | lo p ≤ X p ∧ X p ≤ hi p}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases h : lo p ≤ X p ∧ X p ≤ hi p
    · rw [indicator_of_mem (show X p ∈ Icc (lo p) (hi p) from h),
        indicator_of_mem (show p ∈ {p | lo p ≤ X p ∧ X p ≤ hi p} from h)]
    · rw [indicator_of_notMem (show X p ∉ Icc (lo p) (hi p) from h),
        indicator_of_notMem (show p ∉ {p | lo p ≤ X p ∧ X p ≤ hi p} from h)]
  rw [e]
  exact measurable_const.indicator hs

/-- `krAlive` with a parameter-dependent band `[0, l(p)]`, shift, slope, start and path. -/
theorem measurable_krAlive_band {α : Type*} [MeasurableSpace α] {l y β a : α → ℝ}
    {G : α → ℕ → ℝ} (hl : Measurable l) (hy : Measurable y) (hβ : Measurable β)
    (ha : Measurable a) (hG : Measurable G) (n : ℕ) :
    Measurable (fun p => krAlive (Icc 0 (l p)) (β p) (a p) n (y p) (G p)) := by
  unfold krAlive
  exact Finset.measurable_prod _ fun k _ =>
    measurable_indicator_Icc_param (measurable_kWalk_param hy hβ ha hG k) measurable_const hl

/-! ## The actual strip objects -/

/-- `φ(t) = E e^{-tX}`. -/
def cepsLaplace (ν : ProbabilityMeasure ℝ) (t : ℂ) : ℂ :=
  ∫ x, Complex.exp (-t * x) ∂(ν : Measure ℝ)

/-- `E[e^{-t V_n}; V_0, …, V_n ∈ [0, l]]` for the outer walk `V_n = S_n - n(1+μ)`. -/
def cepsStripTerm (ν : ProbabilityMeasure ℝ) (t : ℂ) (μ l : ℝ) (n : ℕ) : ℂ :=
  ∫ g, (krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 g : ℂ) *
    Complex.exp (-t * kWalk 0 (-(1 + μ)) (-1) g n) ∂(iidLaw ν)

/-- The strip entrance series `H_t(μ, q, l) = ∑ₙ e^{-qn} E[e^{-tV_n}; V_0, …, V_n ∈ [0, l]]`. -/
def cepsStripEntrance (ν : ProbabilityMeasure ℝ) (t : ℂ) (μ : ℝ) (q : ℂ) (l : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * n) * cepsStripTerm ν t μ l n

/-- `k_n^{(μ)}(0, l)`: the pointwise `n`-step density from `0` to `l` of the walk with step
`1 + μ - X`, killed outside `[0, l]`. -/
def cepsBridgeDens (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (μ l : ℝ) (n : ℕ) : ℝ :=
  krDens (Icc 0 l) ν f (1 + μ) 1 n 0 l

/-- The bridge series `U(μ, q, l) = ∑_{n ≥ 1} e^{-qn} k_n^{(μ)}(0, l)`. -/
def cepsBridge (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (μ : ℝ) (q : ℂ) (l : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)

/-- The marked bridge `𝔘(μ, q, l) = ∑_{n ≥ 1} (n - w) e^{-qn} k_n^{(μ)}(0, l)`. -/
def cepsMarkedBridge (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w μ : ℝ) (q : ℂ) (l : ℝ) : ℂ :=
  ∑' n : ℕ, (((n : ℝ) + 1 - w : ℝ) : ℂ) * Complex.exp (-q * ((n : ℂ) + 1)) *
    cepsBridgeDens ν f μ l (n + 1)

/-- The actual pair `J_t(μ) = e^{tl} H_t² 𝔘` at `q = t(1+μ)`, `l = 2ε(1+μ)`. -/
def cepsActualPair (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (t : ℂ) (μ : ℝ) : ℂ :=
  Complex.exp (t * ((2 * eps * (1 + μ) : ℝ) : ℂ)) *
    cepsStripEntrance ν t μ (t * ((1 + μ : ℝ) : ℂ)) (2 * eps * (1 + μ)) ^ 2 *
    cepsMarkedBridge ν f (2 * eps) μ (t * ((1 + μ : ℝ) : ℂ)) (2 * eps * (1 + μ))

end

end PGM
