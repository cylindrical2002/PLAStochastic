import PLAStochastic.Index.CEPS.Jets.ContinuityCumulant
import PLAStochastic.Index.CEPS.Jets.ContinuityContour

/-!
# X8: the first `d` jets on small input classes

Each jet is Lipschitz in the weighted Sobolev distance to `f_Λ` near `f_Λ`
(`cepsJetAt_lipschitz`): the cumulants with Sobolev order `0` (`Jets.ContinuityCumulant`), the
contour jet `(j, m, n)` with Sobolev order `j + 2` (`Jets.ContinuityContour`). The order
`cepsJetContOrderUpTo d` covers the first `d` coordinates of the jet vector, and finitely many
radii and constants combine (`cepsJet_lipschitz_upTo`).

For a law `ν` in `CepsInputClass D θ vlo vhi m η r` the Sobolev density `f` of the class vanishes
on `(-∞, 0)` (it is continuous and agrees a.e. with the `RegLaw` density), and
`cepsJetLaw ν = cepsJet f`. Hence

* `cepsJetLaw_lipschitz_reference`: `|J_i ν - J_i Λ| ≤ C r` for `i < d` and `r ≤ r₀`;
* `cepsJetLaw_mem_reference_box`: for every `ρ > 0` a small class radius puts the first `d` jets
  in the `ρ`-box around `cepsJetLaw cepsLambda`.

The Sobolev order `m` depends only on `d`; `r₀`, `C` and `r` depend on `d`, `η` (and `ρ`).
-/

noncomputable section

open MeasureTheory

namespace PGM

/-- A continuous density of a regular law vanishes on `(-∞, 0)`. -/
theorem RegLaw.eq_zero_of_neg_of_continuous {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hr : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ x, x < 0 → f x = 0 := by
  obtain ⟨f', hf'm, -, hf'0, -, hν'⟩ := hr.density
  have hae : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume] fun x => ENNReal.ofReal (f' x) :=
    (withDensity_eq_iff_of_sigmaFinite hfc.measurable.ennreal_ofReal.aemeasurable
      hf'm.ennreal_ofReal.aemeasurable).mp (hν.symm.trans hν')
  refine eq_zero_of_ae_of_neg hfc (hae.mono fun x hx hx0 => ?_)
  have hx' : ENNReal.ofReal (f x) = ENNReal.ofReal (f' x) := hx
  rw [hf'0 x hx0.le, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero] at hx'
  exact le_antisymm hx' (hf0 x)

/-- The Sobolev order used for the continuity of the jet `i`: `0` for the cumulants, `j + 2`
for the contour jet `(j, m, n)`. -/
def cepsJetContOrder : CepsJetIdx → ℕ
  | .inl _ => 0
  | .inr (j, _, _) => j + 2

/-- A Sobolev order covering the first `d` coordinates of the jet vector. -/
def cepsJetContOrderUpTo (d : ℕ) : ℕ :=
  (Finset.range d).sup fun i => cepsJetContOrder (Denumerable.ofNat CepsJetIdx i)

theorem cepsJetContOrder_le_upTo {d i : ℕ} (hi : i < d) :
    cepsJetContOrder (Denumerable.ofNat CepsJetIdx i) ≤ cepsJetContOrderUpTo d :=
  Finset.le_sup (f := fun i => cepsJetContOrder (Denumerable.ofNat CepsJetIdx i))
    (Finset.mem_range.mpr hi)

/-- **Each jet is Lipschitz near `f_Λ`** in the Sobolev distance of any order `m` at least
`cepsJetContOrder a`, for densities vanishing on `(-∞, 0)`. -/
theorem cepsJetAt_lipschitz (a : CepsJetIdx) {m : ℕ} (hm : cepsJetContOrder a ≤ m) {η : ℝ}
    (hη : 0 < η) (hΛ : CepsSobolevClass m η cepsLambdaDensity) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ f : ℝ → ℝ, (∀ x, x < 0 → f x = 0) →
      CepsSobolevClass m η f → cepsSobolev m η (fun x => f x - cepsLambdaDensity x) ≤ r₀ →
      |cepsJetAt f a - cepsJetAt cepsLambdaDensity a| ≤
        C * cepsSobolev m η (fun x => f x - cepsLambdaDensity x) := by
  rcases a with k | ⟨j, l, n⟩
  · obtain ⟨r₀, C, hr₀, hC, h⟩ := cepsCumulant_lipschitz (k + 2) hη hΛ
    exact ⟨r₀, C, hr₀, hC, fun f _ hf hS => h f hf hS⟩
  · obtain ⟨r₀, C, hr₀, hC, h⟩ := cepsContourJet_lipschitz j l n (N := m) hm hη.le
    refine ⟨r₀, C, hr₀, hC, fun f hneg hf hS => ?_⟩
    have h' := h f hneg (hf.sub hΛ) hS
    simp only [cepsJetAt]
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans h'

/-- **The first `d` jets are uniformly Lipschitz near `f_Λ`.** -/
theorem cepsJet_lipschitz_upTo (d : ℕ) {m : ℕ} (hm : cepsJetContOrderUpTo d ≤ m) {η : ℝ}
    (hη : 0 < η) (hΛ : CepsSobolevClass m η cepsLambdaDensity) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ f : ℝ → ℝ, (∀ x, x < 0 → f x = 0) →
      CepsSobolevClass m η f → cepsSobolev m η (fun x => f x - cepsLambdaDensity x) ≤ r₀ →
      ∀ i : Fin d, |cepsJet f i - cepsJet cepsLambdaDensity i| ≤
        C * cepsSobolev m η (fun x => f x - cepsLambdaDensity x) := by
  have h : ∀ i : Fin d, ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ f : ℝ → ℝ, (∀ x, x < 0 → f x = 0) →
      CepsSobolevClass m η f → cepsSobolev m η (fun x => f x - cepsLambdaDensity x) ≤ r₀ →
      |cepsJet f i - cepsJet cepsLambdaDensity i| ≤
        C * cepsSobolev m η (fun x => f x - cepsLambdaDensity x) := fun i =>
    cepsJetAt_lipschitz (Denumerable.ofNat CepsJetIdx i)
      ((cepsJetContOrder_le_upTo i.isLt).trans hm) hη hΛ
  choose r₀ C hr₀ hC hb using h
  have hsum : 0 ≤ ∑ i, (r₀ i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr₀ i)).le
  refine ⟨(1 + ∑ i, (r₀ i)⁻¹)⁻¹, ∑ i, C i, inv_pos.mpr (by linarith),
    Finset.sum_nonneg fun i _ => hC i, fun f hneg hf hS i => ?_⟩
  have hri : (1 + ∑ i, (r₀ i)⁻¹)⁻¹ ≤ r₀ i := by
    rw [inv_le_comm₀ (by linarith) (hr₀ i)]
    have := Finset.single_le_sum (f := fun i => (r₀ i)⁻¹)
      (fun i _ => (inv_pos.mpr (hr₀ i)).le) (Finset.mem_univ i)
    linarith
  refine (hb i f hneg hf (hS.trans hri)).trans
    (mul_le_mul_of_nonneg_right ?_ (cepsSobolev_nonneg _ _ _))
  exact Finset.single_le_sum (f := C) (fun i _ => hC i) (Finset.mem_univ i)

/-- **The first `d` jets are Lipschitz on small input classes.** There is a Sobolev order `m`
(depending only on `d`) such that for all class constants there are `r₀ > 0` and `C ≥ 0` with
`|J_i ν - J_i Λ| ≤ C r` for every `i < d`, every `r ≤ r₀` and every `ν` in the input class of
radius `r`. -/
theorem cepsJetLaw_lipschitz_reference (d : ℕ) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ r : ℝ, r ≤ r₀ → ∀ ν : ProbabilityMeasure ℝ,
        CepsInputClass D θ vlo vhi m η r ν →
          ∀ i : Fin d, |cepsJetLaw ν i - cepsJetLaw cepsLambda i| ≤ C * r := by
  refine ⟨cepsJetContOrderUpTo d, fun D θ vlo vhi η _ _ _ _ hη => ?_⟩
  by_cases hΛ : CepsSobolevClass (cepsJetContOrderUpTo d) η cepsLambdaDensity
  · obtain ⟨r₀, C, hr₀, hC, h⟩ := cepsJet_lipschitz_upTo d le_rfl hη hΛ
    refine ⟨r₀, C, hr₀, hC, fun r hr ν hν i => ?_⟩
    obtain ⟨f, hf0, hfS, hνf, hS⟩ := hν.density
    have hneg := hν.reg.eq_zero_of_neg_of_continuous hf0 hfS.continuous hνf
    rw [cepsJetLaw_eq_cepsJet hfS.continuous.measurable hf0 hνf,
      cepsJetLaw_eq_cepsJet contDiff_cepsLambdaDensity.continuous.measurable
        cepsLambdaDensity_nonneg cepsLambda_eq_withDensity]
    exact (h f hneg hfS (hS.trans hr) i).trans (mul_le_mul_of_nonneg_left hS hC)
  · exact ⟨1, 0, one_pos, le_rfl, fun r _ ν hν => absurd hν.reference hΛ⟩

/-- **The first `d` jets lie in a reference box on small input classes.** For every `ρ > 0`
there is a Sobolev order `m` (depending only on `d`) such that for all class constants a small
class radius `r` puts the first `d` jets of every law of the class within `ρ` of the reference
jets `cepsJetLaw cepsLambda`. -/
theorem cepsJetLaw_mem_reference_box (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ i : Fin d, |cepsJetLaw ν i - cepsJetLaw cepsLambda i| ≤ ρ := by
  obtain ⟨m, hm⟩ := cepsJetLaw_lipschitz_reference d
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r₀, C, hr₀, hC, h⟩ := hm D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min r₀ (ρ / (C + 1)), lt_min hr₀ (by positivity), fun ν hν i => ?_⟩
  refine (h _ (min_le_left _ _) ν hν i).trans ?_
  calc C * min r₀ (ρ / (C + 1)) ≤ C * (ρ / (C + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ ρ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end PGM
