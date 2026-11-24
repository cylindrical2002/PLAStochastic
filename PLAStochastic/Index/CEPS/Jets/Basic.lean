import PLAStochastic.Index.CEPS.Assembly.Interfaces
import PLAStochastic.Index.CEPS.Canonical.Main
import Mathlib.Logic.Denumerable
import Mathlib.Algebra.Polynomial.Derivative

/-!
# X8: jet functionals on signed densities — basic definitions

For a (signed) density `f` of `X` put `W = 1 - X` and

* `cepsJetTransform f s = ∫ e^{s(1-x)} f(x) dx` (`= E e^{sW}` for a law);
* `cepsJetMoment f k = ∫ (1-x)^k f(x) dx` and the cumulants `cepsCumRec` of the moment sequence
  (Leibniz recursion `κ_{n+1} = m_{n+1} - ∑_{k<n} C(n,k) κ_{k+1} m_{n-k}`, unit mass);
* `cepsJetPoly k = P_k` (`P_0 = X`, `P_{k+1} = (X + X²) P_k'`) and
  `cepsLogDJet k w = -P_k(w/(1-w)) = ∂_x^{k+1} log(1 - e^x w)|_{x=0}`;
* the contour jet `cepsContourJetC c T j m n` on the line `Re s = c` for a transform `T`:
  `m!/(2π) ∫ G_{j,m,n}(s, T s) dy + [j = n = 0, m ≥ 1] (m-1)!`, where
  `G = s^j (-1)^n D_{j+n}(w)/s^{m+1}` (`j + n ≥ 1`) and `G = log((1-w)(s²-1)/s²)/s^{m+1}` (`j = n = 0`).
  For a law it is `∂_q^n ∂_ζ^m ∂_μ^j L(0; 0, 0)` (consistency is proved in `Jets.Consistency`).

The jet index type `CepsJetIdx = ℕ ⊕ (ℕ × ℕ × ℕ)` lists the cumulants `κ_{k+2}` (`inl k`, weight `k`)
and the contour jets `(j, m, n)` (`inr`, weight `j + m + 2n`), coded by `Encodable.encode`.
-/

noncomputable section

open MeasureTheory Complex Polynomial

namespace PGM

/-- The transform `M^f(s) = ∫ e^{s(1-x)} f(x) dx` of a (signed) density `f` of `X`; for a law
with density `f` it is the step transform `E e^{sW}` of `W = 1 - X`. -/
def cepsJetTransform (f : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x : ℝ, cexp (s * (1 - x)) * f x

/-- The moments `∫ (1-x)^k f(x) dx` of `W = 1 - X`. -/
def cepsJetMoment (f : ℝ → ℝ) (k : ℕ) : ℝ := ∫ x : ℝ, (1 - x) ^ k * f x

/-- The moment–cumulant recursion for unit mass:
`κ_{n+1} = m_{n+1} - ∑_{k<n} C(n,k) κ_{k+1} m_{n-k}` (the value `m 0` is not read), `κ_0 = 0`. -/
def cepsCumRec {R : Type*} [CommRing R] (m : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => m (n + 1) - ∑ k : Fin n, (n.choose k : R) * cepsCumRec m (k + 1) * m (n - k)
decreasing_by all_goals (have := k.isLt; omega)

theorem cepsCumRec_zero {R : Type*} [CommRing R] (m : ℕ → R) : cepsCumRec m 0 = 0 := by
  rw [cepsCumRec]

theorem cepsCumRec_succ {R : Type*} [CommRing R] (m : ℕ → R) (n : ℕ) :
    cepsCumRec m (n + 1) = m (n + 1) -
      ∑ k ∈ Finset.range n, (n.choose k : R) * cepsCumRec m (k + 1) * m (n - k) := by
  rw [cepsCumRec, Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : R) * cepsCumRec m (k + 1) * m (n - k)) n]

/-- Ring homomorphisms commute with the cumulant recursion. -/
theorem map_cepsCumRec {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ → R)
    (n : ℕ) : φ (cepsCumRec m n) = cepsCumRec (fun k => φ (m k)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [cepsCumRec_zero]
    · rw [cepsCumRec_succ, cepsCumRec_succ, map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [map_mul, map_mul, map_natCast, ih (k + 1) (by have := Finset.mem_range.mp hk; omega)]

/-- The cumulants of `W` from the moments of a density. -/
def cepsCumulant (f : ℝ → ℝ) (k : ℕ) : ℝ := cepsCumRec (cepsJetMoment f) k

/-- `P_0 = X`, `P_{k+1} = (X + X²) P_k'`: `d/dx P_k(u(x)) = P_{k+1}(u)` when `u' = u + u²`. -/
def cepsJetPoly : ℕ → ℤ[X]
  | 0 => X
  | k + 1 => (X + X ^ 2) * derivative (cepsJetPoly k)

/-- `D_{k+1}(w) = -P_k(w/(1-w)) = ∂_x^{k+1} log(1 - e^x w)|_{x=0}`. -/
def cepsLogDJet (k : ℕ) (w : ℂ) : ℂ := -aeval (w / (1 - w)) (cepsJetPoly k)

/-- The root-free quotient `F̃ = (1 - w)(s² - 1)/s²` (the canonical `F` at the origin). -/
def cepsJetF (s w : ℂ) : ℂ := (1 - w) * (s ^ 2 - 1) / s ^ 2

/-- The integrand `G_{j,m,n}(s, w)` of the contour jet `(j, m, n)`. -/
def cepsJetIntegrand (j m n : ℕ) (s w : ℂ) : ℂ :=
  if j + n = 0 then Complex.log (cepsJetF s w) / s ^ (m + 1)
  else s ^ j * (-1) ^ n * cepsLogDJet (j + n - 1) w / s ^ (m + 1)

/-- The contribution `∂_ζ^m (-log(1 - ζ))|_0 = (m-1)!` of the normalisation (only for
`j = n = 0`, `m ≥ 1`). -/
def cepsJetCorr (j m n : ℕ) : ℂ := if j + n = 0 ∧ m ≠ 0 then ((m - 1).factorial : ℂ) else 0

/-- The contour jet `(j, m, n)` of a transform `T` on the line `Re s = c`. -/
def cepsContourJetC (c : ℝ) (T : ℂ → ℂ) (j m n : ℕ) : ℂ :=
  (m.factorial : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      (∫ y : ℝ, cepsJetIntegrand j m n (c + y * I) (T (c + y * I))) + cepsJetCorr j m n

/-- Jet indices: `inl k` is the cumulant `κ_{k+2}` (`k = 0`: the variance), `inr (j, m, n)` the
contour jet `∂_q^n ∂_ζ^m ∂_μ^j L(0; 0, 0)`. -/
abbrev CepsJetIdx : Type := ℕ ⊕ (ℕ × ℕ × ℕ)

/-- The weight of a jet: `κ_{k+2} ↦ k`, `(j, m, n) ↦ j + m + 2n` (blueprint §5.1). -/
def cepsJetWeight : CepsJetIdx → ℕ
  | .inl k => k
  | .inr (j, m, n) => j + m + 2 * n

/-- The position of a jet in the jet vector. -/
def cepsJetCode (i : CepsJetIdx) : ℕ := Encodable.encode i

theorem ofNat_cepsJetCode (i : CepsJetIdx) : Denumerable.ofNat CepsJetIdx (cepsJetCode i) = i :=
  Denumerable.ofNat_encode i

/-- A finite box containing every jet index of weight at most `k`. -/
def cepsJetIdxBox (k : ℕ) : Finset CepsJetIdx :=
  (Finset.range (k + 1)).map Function.Embedding.inl ∪
    (Finset.range (k + 1) ×ˢ Finset.range (k + 1) ×ˢ Finset.range (k + 1)).map
      Function.Embedding.inr

/-- The number of jet coordinates covering all jets of weight at most `k`. -/
def cepsJetDim (k : ℕ) : ℕ := (cepsJetIdxBox k).sup fun i => cepsJetCode i + 1

theorem mem_cepsJetIdxBox {i : CepsJetIdx} {k : ℕ} (h : cepsJetWeight i ≤ k) :
    i ∈ cepsJetIdxBox k := by
  rcases i with k' | ⟨j, m, n⟩
  · simp only [cepsJetWeight] at h
    simp only [cepsJetIdxBox, Finset.mem_union, Finset.mem_map, Finset.mem_range,
      Function.Embedding.inl_apply]
    exact Or.inl ⟨k', by omega, rfl⟩
  · simp only [cepsJetWeight] at h
    simp only [cepsJetIdxBox, Finset.mem_union, Finset.mem_map, Finset.mem_range,
      Function.Embedding.inr_apply, Finset.mem_product]
    refine Or.inr ⟨(j, m, n), ⟨by omega, show m < k + 1 by omega, show n < k + 1 by omega⟩, rfl⟩

theorem cepsJetCode_lt_cepsJetDim {i : CepsJetIdx} {k : ℕ} (h : cepsJetWeight i ≤ k) :
    cepsJetCode i < cepsJetDim k :=
  Nat.lt_of_succ_le (Finset.le_sup (f := fun i => cepsJetCode i + 1) (mem_cepsJetIdxBox h))

end PGM
