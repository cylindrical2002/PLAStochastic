import PLAStochastic.ForMathlib.Analysis.SpecificLimits.GeometricTracking
import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance
import PLAStochastic.Index.GEP.Additive.HeightOfLogSpan

/-!
# G-EP additive `O(1)`: the assembly from the three analytic inputs

Target (Theorem 3.1a of `notes/height-theorems.md`; proof in
`research/2026-09-28-gep-closure/closure-assembly.md`): under Model G there is a universal
compression ratio `C_ε`, and for each input law there are `ε₀` and `K` with
`|E H - log n / log C_ε| ≤ K` for all `n ≥ 2` and `ε ≥ ε₀`.

This file proves the target **from three named inputs**, which are the results of the
research notes that the assembly consumes.  They are hypotheses here, not theorems:

* `JointResponse` — (J) of `joint-response.md` §1 on every regular class;
* `OrbitClosure` — the layer-map orbit of a regular law stays in one regular class
  (`closure-assembly.md` §3, "正则实际轨道的密度与矩闭合");
* `ShadowDefects P g` — (summable-defects) of `memory-route.md` §7 for the input `g`.

`C_ε` is defined without any hypothesis: `gepLogC ε` is the limit of
`log C_ε(Φ_ε^j Exp(1))`, and `gepC ε = exp (gepLogC ε)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- (J) of `joint-response.md` §1 on the class `RegLaw D θ vlo vhi`: one weight `η` for input
and output, a constant `K`, and a coefficient `a ε → 0` such that for all large `ε` and all
`ν₀, ν₁` in the class
`|Δ log (v C_ε)| ≤ a d_η`, `|Δ v(Φ_ε ·)| ≤ a d_η`, `d_η(Φ_ε ν₀, Φ_ε ν₁) ≤ a d_η + K |Δ v|`.
The first line is written `log v + log C`, which equals `log (v C)` because `v, C > 0` on
the class. -/
def JointResponseOn (D θ vlo vhi : ℝ) : Prop :=
  ∃ η K e0 : ℝ, ∃ a : ℝ → ℝ, 0 < η ∧ η < θ / 4 ∧ 0 ≤ K ∧ (∀ e, 0 ≤ a e) ∧
    Tendsto a atTop (𝓝 0) ∧
    ∀ eps, e0 ≤ eps → ∀ ν₀ ν₁ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν₀ → RegLaw D θ vlo vhi ν₁ →
      |(Real.log (lawVar ν₁) + Real.log (lawC eps ν₁)) -
          (Real.log (lawVar ν₀) + Real.log (lawC eps ν₀))| ≤ a eps * dEta η ν₀ ν₁ ∧
      |lawVar (lawPhi eps ν₁) - lawVar (lawPhi eps ν₀)| ≤ a eps * dEta η ν₀ ν₁ ∧
      dEta η (lawPhi eps ν₀) (lawPhi eps ν₁) ≤
        a eps * dEta η ν₀ ν₁ + K * |lawVar ν₁ - lawVar ν₀|

/-- (J) holds on every regular class. -/
def JointResponse : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → JointResponseOn D θ vlo vhi

/-- Orbits of regular laws stay in one regular class for all large `ε`. -/
def OrbitClosure : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ D' θ' vlo' vhi' e0 : ℝ, 0 < D' ∧ 0 < θ' ∧ 0 < vlo' ∧ vlo' ≤ vhi' ∧
      ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν →
        ∀ j, RegLaw D' θ' vlo' vhi' ((lawPhi eps)^[j] ν)

/-- (summable-defects) of `memory-route.md` §7 for the input gaps `g`: for all large `ε`
there are regular shadow laws `η j` (`j ≥ 1`) with
`∑ W₂(η (j+1), Φ_ε (η j)) ≤ K` and `∑ |log C_j - log C_ε(η j)| ≤ K`,
where `C_j = segMean P ε (epLayerSeq ε g j)` is the actual mean segment length of layer `j`. -/
def ShadowDefects (P : Measure Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∃ D θ vlo vhi K e0 : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
    ∀ eps, e0 ≤ eps → ∃ (η : ℕ → ProbabilityMeasure ℝ) (w : ℕ → ℝ),
      (∀ j, 1 ≤ j → RegLaw D θ vlo vhi (η j)) ∧
      (∀ j, 1 ≤ j → 0 ≤ w j ∧ W2Le (η (j + 1)) (lawPhi eps (η j)) (w j)) ∧
      (∀ L, ∑ j ∈ Ico 1 L, w j ≤ K) ∧
      (∀ L, ∑ j ∈ Ico 1 L,
        |Real.log (segMean P eps (epLayerSeq eps g j)) - Real.log (lawC eps (η j))| ≤ K)

/-- `log C_ε`: the limit of `log C_ε` along the layer-map orbit of `Exp(1)`. -/
def gepLogC (eps : ℝ) : ℝ :=
  limUnder atTop (fun j : ℕ => Real.log (lawC eps ((lawPhi eps)^[j] expPM)))

/-- The universal compression ratio `C_ε`. -/
def gepC (eps : ℝ) : ℝ := Real.exp (gepLogC eps)

/-! ## The contraction metric and the tracking bound (`closure-assembly.md` §2–3) -/

/-- The weighted distance `λ |Δ v| + d_η` of `closure-assembly.md` §2. -/
def gepDist (lam η : ℝ) (ν ρ : ProbabilityMeasure ℝ) : ℝ :=
  lam * |lawVar ν - lawVar ρ| + dEta η ν ρ

theorem gepDist_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (η : ℝ) (ν ρ : ProbabilityMeasure ℝ) :
    0 ≤ gepDist lam η ν ρ :=
  add_nonneg (mul_nonneg hlam (abs_nonneg _)) (dEta_nonneg η ν ρ)

theorem gepDist_self (lam η : ℝ) (ν : ProbabilityMeasure ℝ) : gepDist lam η ν ν = 0 := by
  simp [gepDist, dEta_self]

theorem gepDist_triangle {D θ vlo vhi lam η : ℝ} {μ ν ρ : ProbabilityMeasure ℝ}
    (hμ : RegLaw D θ vlo vhi μ) (hν : RegLaw D θ vlo vhi ν) (hρ : RegLaw D θ vlo vhi ρ)
    (hlam : 0 ≤ lam) (hη : 0 ≤ η) (hηθ : η < θ) :
    gepDist lam η μ ρ ≤ gepDist lam η μ ν + gepDist lam η ν ρ := by
  unfold gepDist
  have h1 := mul_le_mul_of_nonneg_left (abs_sub_le (lawVar μ) (lawVar ν) (lawVar ρ)) hlam
  have h2 := dEta_triangle hμ hν hρ hη hηθ
  linarith

theorem gepDist_le_diam {D θ vlo vhi lam η : ℝ} {ν ρ : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hρ : RegLaw D θ vlo vhi ρ) (hlam : 0 ≤ lam) (hη : 0 ≤ η)
    (hηθ : η < θ) : gepDist lam η ν ρ ≤ lam * (vhi - vlo) + D / (θ * (θ - η)) := by
  unfold gepDist
  have h1 := mul_le_mul_of_nonneg_left (abs_lawVar_sub_le_diam hν hρ) hlam
  have h2 := dEta_le_diam hν hρ hη hηθ
  linarith

theorem gepDist_le_of_W2Le {D θ vlo vhi lam η w : ℝ} {ν ρ : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hρ : RegLaw D θ vlo vhi ρ) (hlam : 0 ≤ lam) (hvhi : 0 ≤ vhi)
    (hη : 0 ≤ η) (h2η : 2 * η < θ) (hw0 : 0 ≤ w) (hw : W2Le ν ρ w) :
    gepDist lam η ν ρ ≤ (lam * (2 * Real.sqrt vhi) + Real.sqrt (2 * D / (θ - 2 * η))) * w := by
  unfold gepDist
  have h1 := mul_le_mul_of_nonneg_left (abs_lawVar_sub_le_of_W2Le hν hρ hvhi hw0 hw) hlam
  have h2 := dEta_le_of_W2Le hν hρ hη h2η hw0 hw
  calc lam * |lawVar ν - lawVar ρ| + dEta η ν ρ
      ≤ lam * (2 * Real.sqrt vhi * w) + Real.sqrt (2 * D / (θ - 2 * η)) * w := add_le_add h1 h2
    _ = (lam * (2 * Real.sqrt vhi) + Real.sqrt (2 * D / (θ - 2 * η))) * w := by ring

/-- (C) of `closure-assembly.md` §2: lines 2–3 of (J) make `Φ_ε` halve `gepDist`. -/
theorem gepDist_lawPhi_le {lam η K a eps : ℝ} {ν ρ : ProbabilityMeasure ℝ}
    (hlam : 0 ≤ lam) (hK : K ≤ lam / 2) (ha : (lam + 1) * a ≤ 1 / 2)
    (hv : |lawVar (lawPhi eps ρ) - lawVar (lawPhi eps ν)| ≤ a * dEta η ν ρ)
    (hd : dEta η (lawPhi eps ν) (lawPhi eps ρ) ≤
      a * dEta η ν ρ + K * |lawVar ρ - lawVar ν|) :
    gepDist lam η (lawPhi eps ν) (lawPhi eps ρ) ≤ gepDist lam η ν ρ / 2 := by
  unfold gepDist
  rw [abs_sub_comm (lawVar (lawPhi eps ν))]
  rw [abs_sub_comm (lawVar ρ)] at hd
  have hD : 0 ≤ dEta η ν ρ := dEta_nonneg _ _ _
  have hV : 0 ≤ |lawVar ν - lawVar ρ| := abs_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hv hlam
  have h2 := mul_le_mul_of_nonneg_right ha hD
  have h3 := mul_le_mul_of_nonneg_right hK hV
  linarith

/-- (L) of `closure-assembly.md` §1: line 1 of (J) and `v ≥ v₋` make `log C_ε` Lipschitz
for `gepDist`. -/
theorem abs_log_lawC_sub_le {vlo lam η a eps Lc : ℝ} {ν ρ : ProbabilityMeasure ℝ}
    (hvlo : 0 < vlo) (hlam : 0 < lam) (hLc1 : 1 ≤ Lc) (hLc2 : 1 / (lam * vlo) ≤ Lc)
    (hν : vlo ≤ lawVar ν) (hρ : vlo ≤ lawVar ρ) (ha1 : a ≤ 1)
    (h : |(Real.log (lawVar ρ) + Real.log (lawC eps ρ)) -
      (Real.log (lawVar ν) + Real.log (lawC eps ν))| ≤ a * dEta η ν ρ) :
    |Real.log (lawC eps ν) - Real.log (lawC eps ρ)| ≤ Lc * gepDist lam η ν ρ := by
  unfold gepDist
  have hD : 0 ≤ dEta η ν ρ := dEta_nonneg _ _ _
  have hV : 0 ≤ |lawVar ν - lawVar ρ| := abs_nonneg _
  have hlog := abs_log_sub_log_le hvlo hρ hν
  rw [abs_sub_comm (lawVar ρ)] at hlog
  have e : |lawVar ν - lawVar ρ| / vlo = 1 / (lam * vlo) * (lam * |lawVar ν - lawVar ρ|) := by
    field_simp
  have h1 : |lawVar ν - lawVar ρ| / vlo ≤ Lc * (lam * |lawVar ν - lawVar ρ|) := by
    rw [e]; exact mul_le_mul_of_nonneg_right hLc2 (by positivity)
  have h2 : dEta η ν ρ ≤ Lc * dEta η ν ρ := le_mul_of_one_le_left hD hLc1
  have h3 : a * dEta η ν ρ ≤ dEta η ν ρ := mul_le_of_le_one_left hD ha1
  obtain ⟨hl1, hl2⟩ := abs_le.mp h
  obtain ⟨hm1, hm2⟩ := abs_le.mp hlog
  rw [abs_le]
  constructor <;> nlinarith

/-- Two orbits in a class on which `Φ` halves `d` approach at rate `diam / 2^i`. -/
theorem orbit_dist_le {α : Type*} (Φ : α → α) (d : α → α → ℝ) (S : α → Prop) {Dst : ℝ}
    (hcon : ∀ x y, S x → S y → d (Φ x) (Φ y) ≤ d x y / 2)
    (hdiam : ∀ x y, S x → S y → d x y ≤ Dst) {x y : α}
    (hx : ∀ i, S (Φ^[i] x)) (hy : ∀ i, S (Φ^[i] y)) (i : ℕ) :
    d (Φ^[i] x) (Φ^[i] y) ≤ Dst / 2 ^ i := by
  have h := orbit_contract Φ d x y (fun i => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hcon _ _ (hx i) (hy i)) i
  have h0 : d x y ≤ Dst := hdiam x y (hx 0) (hy 0)
  calc d (Φ^[i] x) (Φ^[i] y) ≤ d x y / 2 ^ i := h
    _ ≤ Dst / 2 ^ i := by gcongr

/-- The abstract assembly of `closure-assembly.md` §2–3: a contraction on a class of finite
diameter, a Lipschitz scalar `F`, and a pseudo-orbit `η` with summable defects give
`∑ |A j - lim F(Φ^j x₀)| ≤ K + 2 Lc Kw K + 4 Lc Dst`. -/
theorem sum_abs_sub_limUnder_le {α : Type*} (Φ : α → α) (d : α → α → ℝ) (F : α → ℝ)
    (S : α → Prop) (x₀ : α) (η : ℕ → α) (w A : ℕ → ℝ) {Lc Dst Kw K : ℝ}
    (hLc : 0 ≤ Lc) (hDst : 0 ≤ Dst) (hKw : 0 ≤ Kw)
    (hd0 : ∀ x y, 0 ≤ d x y) (hdself : ∀ x, d x x = 0)
    (htri : ∀ x y z, S x → S y → S z → d x z ≤ d x y + d y z)
    (hcon : ∀ x y, S x → S y → d (Φ x) (Φ y) ≤ d x y / 2)
    (hdiam : ∀ x y, S x → S y → d x y ≤ Dst)
    (hlip : ∀ x y, S x → S y → |F x - F y| ≤ Lc * d x y)
    (hx₀ : ∀ i, S (Φ^[i] x₀)) (hσ : ∀ i, S (Φ^[i] (η 1)))
    (hη : ∀ j, 1 ≤ j → S (η j)) (hΦη : ∀ j, 1 ≤ j → S (Φ (η j)))
    (hδ : ∀ j, 1 ≤ j → d (η (j + 1)) (Φ (η j)) ≤ Kw * w j)
    (hw : ∀ L, ∑ j ∈ Ico 1 L, w j ≤ K) (hA : ∀ L, ∑ j ∈ Ico 1 L, |A j - F (η j)| ≤ K)
    (L : ℕ) :
    ∑ j ∈ Ico 1 L, |A j - limUnder atTop (fun j : ℕ => F (Φ^[j] x₀))| ≤
      K + Lc * (2 * (Kw * K)) + 4 * (Lc * Dst) := by
  -- the scalar sequence along the reference orbit is geometrically Cauchy
  have hr : ∀ j k, j ≤ k → |F (Φ^[j] x₀) - F (Φ^[k] x₀)| ≤ Lc * Dst / 2 ^ j := by
    intro j k hjk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have hy : ∀ i, S (Φ^[i] (Φ^[m] x₀)) := fun i => by
      rw [← Function.iterate_add_apply]; exact hx₀ _
    have h1 := orbit_dist_le Φ d S hcon hdiam hx₀ hy j
    rw [Function.iterate_add_apply]
    calc |F (Φ^[j] x₀) - F (Φ^[j] (Φ^[m] x₀))|
        ≤ Lc * d (Φ^[j] x₀) (Φ^[j] (Φ^[m] x₀)) := hlip _ _ (hx₀ j) (hy j)
      _ ≤ Lc * (Dst / 2 ^ j) := mul_le_mul_of_nonneg_left h1 hLc
      _ = Lc * Dst / 2 ^ j := by ring
  obtain ⟨c, hcT, hc⟩ := geometric_cauchy_limit hr
  rw [hcT.limUnder_eq]
  -- the true orbit of `η 1` has the same limit, at the same rate
  have hσc : ∀ i, |F (Φ^[i] (η 1)) - c| ≤ 2 * (Lc * Dst) / 2 ^ i := by
    intro i
    have h1 := hlip _ _ (hσ i) (hx₀ i)
    have h2 := mul_le_mul_of_nonneg_left (orbit_dist_le Φ d S hcon hdiam hσ hx₀ i) hLc
    have h3 := hc i
    have h4 := abs_sub_le (F (Φ^[i] (η 1))) (F (Φ^[i] x₀)) c
    have e : 2 * (Lc * Dst) / 2 ^ i = Lc * (Dst / 2 ^ i) + Lc * Dst / 2 ^ i := by ring
    rw [e]
    linarith
  -- tracking the pseudo-orbit `η` by the true orbit of `η 1`
  have hrec : ∀ j, 1 ≤ j → d (η (j + 1)) (Φ^[j + 1 - 1] (η 1)) ≤
      d (η (j + 1)) (Φ (η j)) + d (η j) (Φ^[j - 1] (η 1)) / 2 := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Function.iterate_succ_apply']
    have ht := htri (η (i + 1 + 1)) (Φ (η (i + 1))) (Φ (Φ^[i] (η 1))) (hη _ (by omega))
      (hΦη _ (by omega)) (by rw [← Function.iterate_succ_apply' Φ i]; exact hσ _)
    have hc' := hcon _ _ (hη _ (by omega)) (hσ i)
    linarith
  have htr := tracking_sum (b := fun j => d (η j) (Φ^[j - 1] (η 1)))
    (δ := fun j => d (η (j + 1)) (Φ (η j))) (fun j => hd0 _ _) (hdself _) hrec L
  have hδsum : ∑ j ∈ Ico 1 L, d (η (j + 1)) (Φ (η j)) ≤ Kw * K := by
    calc ∑ j ∈ Ico 1 L, d (η (j + 1)) (Φ (η j)) ≤ ∑ j ∈ Ico 1 L, Kw * w j :=
          Finset.sum_le_sum (fun j hj => hδ j (Finset.mem_Ico.mp hj).1)
      _ = Kw * ∑ j ∈ Ico 1 L, w j := (Finset.mul_sum _ _ _).symm
      _ ≤ Kw * K := mul_le_mul_of_nonneg_left (hw L) hKw
  -- the per-layer bound
  have hterm : ∀ j ∈ Ico 1 L, |A j - c| ≤
      |A j - F (η j)| + Lc * d (η j) (Φ^[j - 1] (η 1)) + 2 * (Lc * Dst) / 2 ^ (j - 1) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have h1 := hlip _ _ (hη j hj1) (hσ (j - 1))
    have h2 := hσc (j - 1)
    have e1 := abs_sub_le (A j) (F (η j)) c
    have e2 := abs_sub_le (F (η j)) (F (Φ^[j - 1] (η 1))) c
    linarith
  have hgeom : ∑ j ∈ Ico 1 L, 2 * (Lc * Dst) / 2 ^ (j - 1) ≤ 4 * (Lc * Dst) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    have := sum_geometric_le (M := 2 * (Lc * Dst)) (by positivity) (L - 1)
    linarith
  have hbK : Lc * ∑ j ∈ Ico 1 L, d (η j) (Φ^[j - 1] (η 1)) ≤ Lc * (2 * (Kw * K)) :=
    mul_le_mul_of_nonneg_left (by linarith) hLc
  calc ∑ j ∈ Ico 1 L, |A j - c|
      ≤ ∑ j ∈ Ico 1 L, (|A j - F (η j)| + Lc * d (η j) (Φ^[j - 1] (η 1)) +
          2 * (Lc * Dst) / 2 ^ (j - 1)) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Ico 1 L, |A j - F (η j)| + Lc * ∑ j ∈ Ico 1 L, d (η j) (Φ^[j - 1] (η 1)) +
          ∑ j ∈ Ico 1 L, 2 * (Lc * Dst) / 2 ^ (j - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ K + Lc * (2 * (Kw * K)) + 4 * (Lc * Dst) := by linarith [hA L]

/-- Two regular classes sit in a common one. -/
theorem exists_regLaw_join {D₁ θ₁ vlo₁ vhi₁ D₂ θ₂ vlo₂ vhi₂ : ℝ} (hD : 0 < D₁) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (hvlo₁ : 0 < vlo₁) (hvlo₂ : 0 < vlo₂) (hv₁ : vlo₁ ≤ vhi₁) :
    ∃ D θ vlo vhi : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      (∀ ν, RegLaw D₁ θ₁ vlo₁ vhi₁ ν → RegLaw D θ vlo vhi ν) ∧
      (∀ ν, RegLaw D₂ θ₂ vlo₂ vhi₂ ν → RegLaw D θ vlo vhi ν) :=
  ⟨max D₁ D₂, min θ₁ θ₂, min vlo₁ vlo₂, max vhi₁ vhi₂, lt_max_of_lt_left hD, lt_min hθ₁ hθ₂,
    lt_min hvlo₁ hvlo₂, (min_le_left _ _).trans (hv₁.trans (le_max_left _ _)),
    fun _ h => h.mono (le_max_left _ _) (min_le_left _ _) (lt_min hθ₁ hθ₂).le (min_le_left _ _)
      (le_max_left _ _),
    fun _ h => h.mono (le_max_right _ _) (min_le_right _ _) (lt_min hθ₁ hθ₂).le
      (min_le_right _ _) (le_max_right _ _)⟩

/-- (FP-strong) of `closure-assembly.md` §3, from the three inputs. -/
theorem sum_abs_log_segMean_sub_le_of_inputs (hJ : JointResponse) (hC : OrbitClosure)
    [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hS : ShadowDefects P g) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K := by
  -- the input law enters only through the shadow defects `hS`; `hg` is kept for the interface
  have _ := hg
  obtain ⟨DS, θS, vloS, vhiS, KS, eS, hDS, hθS, hvloS, hvS, hSh⟩ := hS
  obtain ⟨D1, θ1, vlo1, vhi1, e1, hD1, hθ1, hvlo1, hv1, hC1⟩ :=
    hC DS θS vloS vhiS hDS hθS hvloS hvS
  obtain ⟨D2, θ2, vlo2, vhi2, e2, -, hθ2, hvlo2, -, hC2⟩ :=
    hC 1 1 1 1 one_pos one_pos one_pos le_rfl
  -- one regular class containing the shadows, their orbits, and the orbit of `Exp(1)`
  obtain ⟨D', θ', vlo', vhi', hD', hθ', hvlo', hv', incS', inc1'⟩ :=
    exists_regLaw_join hDS hθS hθ1 hvloS hvlo1 hvS
  obtain ⟨Ds, θs, vlos, vhis, hDs, hθs, hvlos, hvs, inc', inc2⟩ :=
    exists_regLaw_join hD' hθ' hθ2 hvlo' hvlo2 hv'
  have incS : ∀ ν, RegLaw DS θS vloS vhiS ν → RegLaw Ds θs vlos vhis ν :=
    fun ν h => inc' ν (incS' ν h)
  have inc1 : ∀ ν, RegLaw D1 θ1 vlo1 vhi1 ν → RegLaw Ds θs vlos vhis ν :=
    fun ν h => inc' ν (inc1' ν h)
  obtain ⟨ηJ, KJ, eJ, a, hη0, hηθ, hKJ, ha0, haT, hJs⟩ := hJ Ds θs vlos vhis hDs hθs hvlos hvs
  -- the metric `lam |Δ v| + d_η` and its constants
  obtain ⟨lam, hlam0, hKlam⟩ : ∃ lam : ℝ, 0 < lam ∧ KJ ≤ lam / 2 :=
    ⟨2 * KJ + 1, by linarith, by linarith⟩
  obtain ⟨Lc, hLc1, hLc2⟩ : ∃ Lc : ℝ, 1 ≤ Lc ∧ 1 / (lam * vlos) ≤ Lc :=
    ⟨max 1 (1 / (lam * vlos)), le_max_left _ _, le_max_right _ _⟩
  have hηθs : ηJ < θs := by linarith
  have h2ηθs : 2 * ηJ < θs := by linarith
  obtain ⟨Dst, hDst0, hdiam⟩ : ∃ Dst : ℝ, 0 ≤ Dst ∧ ∀ ν ρ, RegLaw Ds θs vlos vhis ν →
      RegLaw Ds θs vlos vhis ρ → gepDist lam ηJ ν ρ ≤ Dst := by
    refine ⟨lam * (vhis - vlos) + Ds / (θs * (θs - ηJ)), ?_,
      fun ν ρ hν hρ => gepDist_le_diam hν hρ hlam0.le hη0.le hηθs⟩
    have : 0 < θs - ηJ := by linarith
    have : 0 ≤ vhis - vlos := by linarith
    positivity
  obtain ⟨Kw, hKw0, hKw⟩ : ∃ Kw : ℝ, 0 ≤ Kw ∧ ∀ ν ρ w, RegLaw Ds θs vlos vhis ν →
      RegLaw Ds θs vlos vhis ρ → 0 ≤ w → W2Le ν ρ w → gepDist lam ηJ ν ρ ≤ Kw * w :=
    ⟨lam * (2 * Real.sqrt vhis) + Real.sqrt (2 * Ds / (θs - 2 * ηJ)), by positivity,
      fun ν ρ w hν hρ hw0 hw => gepDist_le_of_W2Le hν hρ hlam0.le (hvlos.le.trans hvs) hη0.le
        h2ηθs hw0 hw⟩
  -- the contraction threshold
  obtain ⟨e3, he3⟩ : ∃ e3 : ℝ, ∀ eps, e3 ≤ eps → (lam + 1) * a eps ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < 1 / (2 * (lam + 1)) := by positivity
    obtain ⟨e3, he3⟩ := eventually_atTop.mp (haT.eventually_le_const hpos)
    refine ⟨e3, fun eps h => ?_⟩
    calc (lam + 1) * a eps ≤ (lam + 1) * (1 / (2 * (lam + 1))) :=
          mul_le_mul_of_nonneg_left (he3 eps h) (by linarith)
      _ = 1 / 2 := by field_simp
  refine ⟨max eS (max e1 (max e2 (max eJ e3))), KS + Lc * (2 * (Kw * KS)) + 4 * (Lc * Dst), ?_⟩
  intro eps heps L
  simp only [max_le_iff] at heps
  obtain ⟨heS, he1, he2, heJ, he3'⟩ := heps
  obtain ⟨η, w, hηreg, hw, hwsum, hlogsum⟩ := hSh eps heS
  have ha1 := he3 eps he3'
  have ha0' := ha0 eps
  have ha_le1 : a eps ≤ 1 := by nlinarith
  exact sum_abs_sub_limUnder_le (lawPhi eps) (gepDist lam ηJ) (fun ν => Real.log (lawC eps ν))
    (RegLaw Ds θs vlos vhis) expPM η w
    (fun j => Real.log (segMean P eps (epLayerSeq eps g j))) (by linarith) hDst0 hKw0
    (fun _ _ => gepDist_nonneg hlam0.le _ _ _) (fun _ => gepDist_self _ _ _)
    (fun _ _ _ hx hy hz => gepDist_triangle hx hy hz hlam0.le hη0.le hηθs)
    (fun x y hx hy => by
      obtain ⟨-, h2, h3⟩ := hJs eps heJ x y hx hy
      exact gepDist_lawPhi_le hlam0.le hKlam ha1 h2 h3)
    hdiam
    (fun x y hx hy => by
      obtain ⟨h1, -, -⟩ := hJs eps heJ x y hx hy
      exact abs_log_lawC_sub_le hvlos hlam0 hLc1 hLc2 hx.var_ge hy.var_ge ha_le1 h1)
    (fun i => inc2 _ (hC2 eps he2 expPM regLaw_expPM i))
    (fun i => inc1 _ (hC1 eps he1 (η 1) (hηreg 1 le_rfl) i))
    (fun j hj => incS _ (hηreg j hj))
    (fun j hj => inc1 _ (hC1 eps he1 (η j) (hηreg j hj) 1))
    (fun j hj => hKw _ _ _ (incS _ (hηreg (j + 1) (by omega)))
      (inc1 _ (hC1 eps he1 (η j) (hηreg j hj) 1)) (hw j hj).1 (hw j hj).2)
    hwsum hlogsum L

/-- **G-EP additive `O(1)`, from the three inputs.** -/
theorem H_G_EP_additive_of_inputs (hJ : JointResponse) (hC : OrbitClosure)
    [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hS : ShadowDefects P g) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K := by
  obtain ⟨e1, KF, hF⟩ := sum_abs_log_segMean_sub_le_of_inputs hJ hC hg hS
  obtain ⟨cb, hcb_def⟩ : ∃ cb, cb = cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := ⟨_, rfl⟩
  have hcb1 : 1 ≤ cb := hcb_def ▸ one_le_cBr (bAbs_le_bIn μ₀ σ₀)
  have hcb0 : 0 < cb := by linarith
  refine ⟨max e1 (max (epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))))
    (max (2 * cb) (Real.exp ((1 + Real.log cb + KF) / 2)))),
    2 * Real.log cb + 2 * KF + Real.log 2 + 4 * KcIn + 3, ?_⟩
  intro eps heps n hn
  simp only [max_le_iff] at heps
  obtain ⟨he1, he₀, hecb, heX⟩ := heps
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) he₀
  have heps0 : 0 < eps := by linarith
  have heps2 : 0 < eps ^ 2 := by positivity
  -- the per-layer bracket in logarithmic form
  have hlogbr : ∀ ℓ, Real.log (eps ^ 2) - Real.log cb ≤
      Real.log (segMean P eps (epLayerSeq eps g ℓ)) ∧
      Real.log (segMean P eps (epLayerSeq eps g ℓ)) ≤ Real.log cb + Real.log (eps ^ 2) := by
    intro ℓ
    obtain ⟨h1, h2⟩ := segMean_bracket hg he₀ ℓ
    rw [← hcb_def] at h1 h2
    have hpos : 0 < eps ^ 2 / cb := div_pos heps2 hcb0
    constructor
    · rw [← Real.log_div heps2.ne' hcb0.ne']; exact Real.log_le_log hpos h1
    · rw [← Real.log_mul hcb0.ne' heps2.ne']; exact Real.log_le_log (hpos.trans_le h1) h2
  -- the first shadow layer pins `c = log C_ε` to `2 log ε + O(1)`
  have hC1 : |Real.log (segMean P eps (epLayerSeq eps g 1)) - gepLogC eps| ≤ KF := by
    have h := hF eps he1 2
    rwa [Finset.sum_Ico_eq_sum_range, show (2 : ℕ) - 1 = 1 from rfl, Finset.sum_range_one]
      at h
  have hKF : 0 ≤ KF := (abs_nonneg _).trans hC1
  have hlogeps : (1 + Real.log cb + KF) / 2 ≤ Real.log eps := by
    have h := Real.log_le_log (Real.exp_pos _) heX
    rwa [Real.log_exp] at h
  have hle2 : Real.log (eps ^ 2) = 2 * Real.log eps := by
    rw [Real.log_pow]; norm_num
  have hc1 : 1 ≤ gepLogC eps := by
    have := (hlogbr 1).1
    have := (abs_le.mp hC1).2
    linarith
  have hC0 : |Real.log (segMean P eps (epLayerSeq eps g 0)) - gepLogC eps| ≤
      2 * Real.log cb + KF := by
    have := hlogbr 0
    have := hlogbr 1
    have := abs_le.mp hC1
    rw [abs_le]; constructor <;> linarith
  -- `log m_ℓ = ℓ c + O(1)`
  have hlog : ∀ ℓ : ℕ, |Real.log (meanSpan P eps g ℓ) - ℓ * gepLogC eps| ≤
      2 * Real.log cb + 2 * KF := by
    intro ℓ
    rw [log_meanSpan_eq_sum hg he₀ ℓ]
    have e : ∑ j ∈ range ℓ, Real.log (segMean P eps (epLayerSeq eps g j)) - ℓ * gepLogC eps =
        ∑ j ∈ range ℓ, (Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hlcb : 0 ≤ Real.log cb := Real.log_nonneg hcb1
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hpos, zero_add]
      have := hF eps he1 ℓ
      linarith
  have hbig : 2 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2 := by
    rw [← hcb_def]; nlinarith
  have hmain := integral_epHeight_additive_of_logSpan hg x0 he₀ hbig (by linarith) hlog hn
  have hgc : Real.log (gepC eps) = gepLogC eps := Real.log_exp _
  rw [hgc]
  have hB : (2 * Real.log cb + 2 * KF) / gepLogC eps ≤ 2 * Real.log cb + 2 * KF :=
    div_le_self (by linarith [Real.log_nonneg hcb1]) hc1
  have hl2 : Real.log 2 / gepLogC eps ≤ Real.log 2 :=
    div_le_self (Real.log_nonneg one_le_two) hc1
  linarith

end

end PGM
