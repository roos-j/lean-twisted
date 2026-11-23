/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file was assembled by Claude from the statement files
`TwistedParaproduct/Auto/Defs.lean` and `TwistedParaproduct/Auto/Theorems.lean`
(whose statements were checked against the manuscript by the author), together
with the Mikhlin condition from `LeanSpherical/Auto/MikhlinHormander.lean` in the
`lean-spherical` dependency. The docstrings on the definitions and theorems were
written by Claude.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Challenge file for Comparator
-/

public section

/-! ## The Mikhlin condition (copied from `lean-spherical`) -/

namespace Auto.Spherical.SurfaceMeasureDecay

/-- The real Euclidean space of dimension `d`. -/
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

end Auto.Spherical.SurfaceMeasureDecay

namespace Auto.MikhlinHormander

open Auto.Spherical.SurfaceMeasureDecay

/-- The coordinate-free Mikhlin seminorm condition: for every order `k ≤ N` and
every `ξ ≠ 0`, `‖ξ‖^k ‖D^k m(ξ)‖ ≤ C`. -/
@[expose] def aux_MikhlinCondition {d : Nat} (N : Nat) (m : Euclidean d → Complex)
    (C : Real) : Prop :=
  ∀ k ≤ N, ∀ ξ : Euclidean d, ξ ≠ 0 →
    ‖ξ‖ ^ k * ‖iteratedFDeriv Real k m ξ‖ ≤ C

/-- The Mikhlin condition of order `N` with constant `C`: `m` is `N` times
continuously differentiable away from the origin and satisfies the derivative
bounds of `aux_MikhlinCondition`. -/
@[expose] def MikhlinCondition {d : Nat} (N : Nat) (m : Euclidean d → Complex)
    (C : Real) : Prop :=
  ContDiffOn Real N m ({0}ᶜ : Set (Euclidean d)) ∧
  aux_MikhlinCondition N m C

end Auto.MikhlinHormander

/-! ## Twisted paraproduct operators (copied from `TwistedParaproduct/Auto/Defs.lean`) -/

namespace Auto

-- `Defs.lean` is elaborated without this instance in scope; removing it locally
-- makes these definitions elaborate to the same terms as in the solution.
attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Filter Topology Set SchwartzMap
open scoped BigOperators FourierTransform

/-- Real Euclidean space `ℝ^n`. -/
scoped notation:max "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

/-- The `i`th standard unit vector. -/
@[expose] noncomputable abbrev unitVector {d : ℕ} (i : Fin d) : ℝ^d :=
  EuclideanSpace.single i (1 : ℝ)

/-- The multiplier sees coordinate `j` of the frequency of input `j`:
`diagonalFrequency ξ = (ξ₁₁, ξ₂₂, …, ξ_dd)`. -/
@[expose] def diagonalFrequency {d : ℕ} (ξ : Fin d → ℝ^d) : ℝ^d :=
  WithLp.toLp 2 (fun j => ξ j j)

/-- The integrand `m(ξ₁₁,…,ξ_dd) ∏ᵢ f̂ᵢ(ξᵢ) e^{2πi x·(ξ₁+⋯+ξ_d)}` of the twisted
operator. (Kept so that `twisted` elaborates to the same term as in the solution.) -/
@[expose] noncomputable def fourierIntegrand {d : ℕ} (m : ℝ^d → ℂ)
    (f : Fin d → 𝓢(ℝ^d, ℂ)) (x : ℝ^d) (ξ : Fin d → ℝ^d) : ℂ :=
  m (diagonalFrequency ξ) * (∏ j, (𝓕 (f j)) (ξ j)) *
    Complex.exp (Complex.I * Complex.ofReal
      (2 * Real.pi * inner ℝ x (∑ j, ξ j)))

/-- The twisted Fourier multiplier operator
`T_m(f₁,…,f_d)(x) = ∫ m(ξ₁₁,…,ξ_dd) ∏ᵢ f̂ᵢ(ξᵢ) e^{2πi x·(ξ₁+⋯+ξ_d)} dξ`. -/
@[expose] noncomputable def twisted {d : ℕ} (m : ℝ^d → ℂ)
    (f : Fin d → 𝓢(ℝ^d, ℂ)) (x : ℝ^d) : ℂ :=
  ∫ ξ : Fin d → ℝ^d,
    m (diagonalFrequency ξ) * (∏ i, (𝓕 (f i)) (ξ i)) *
      Complex.exp (Complex.I * Complex.ofReal (2 * Real.pi * inner ℝ x (∑ i, ξ i)))

/-- The physical-space form `∫ L(y) ∏ᵢ fᵢ(x - yᵢ eᵢ) dy`. -/
@[expose] noncomputable def physicalKernelApply {d : ℕ} (L : ℝ^d → ℂ)
    (f : Fin d → ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, L y * ∏ i, f i (x - y i • unitVector i)

/-- The kernel `K` restricted to the open annulus `ε < ‖x‖ < R`. -/
@[expose] noncomputable def hardAnnulus {d : ℕ} (K : ℝ^d → ℂ) (ε R : ℝ) : ℝ^d → ℂ :=
  {x : ℝ^d | ε < ‖x‖ ∧ ‖x‖ < R}.indicator K

/-- The homogeneous extension `K(y) = ‖y‖^{-d} Ω(y/‖y‖)` of a function `Ω` on the
unit sphere, with `K(0) = 0`. -/
@[expose] noncomputable def homogeneousKernel {d : ℕ}
    (Ω : Metric.sphere (0 : ℝ^d) 1 → ℂ) (y : ℝ^d) : ℂ :=
  if hy : y = 0 then 0 else
    (↑(‖y‖⁻¹^d):ℂ) * Ω ((homeomorphUnitSphereProd (ℝ^d) ⟨y,hy⟩).1)

/-- The compensated integrand `K(y) (g(y) - 1_{‖y‖ ≤ 1} g(0))` of the principal
value pairing. -/
@[expose] noncomputable def compensatedPrincipalValue {d : ℕ} (K g : ℝ^d → ℂ)
    (y : ℝ^d) : ℂ :=
  K y * (g y - {z : ℝ^d | ‖z‖ ≤ 1}.indicator (fun _ => g 0) y)

/-- The filter `ε → 0⁺, R → ∞` on pairs `(ε, R)`. -/
@[expose] noncomputable def hardEndpointFilter : Filter (ℝ × ℝ) :=
  (𝓝[>] (0:ℝ)) ×ˢ atTop

/-- The hard truncation of the operator with kernel `K` to the annulus `ε < ‖y‖ < R`. -/
@[expose] noncomputable def T_trunc {d : ℕ} (K : ℝ^d → ℂ) (f : Fin d → ℝ^d → ℂ)
    (x : ℝ^d) (ε R : ℝ) : ℂ :=
  physicalKernelApply (hardAnnulus K ε R) f x

/-- The joint spherical principal value as the inner radius tends to zero and
the outer radius tends to infinity. -/
@[expose] noncomputable def T {d : ℕ} (K : ℝ^d → ℂ) (f : Fin d → ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  limUnder hardEndpointFilter (fun a : ℝ × ℝ ↦ T_trunc K f x a.1 a.2)

end Auto

/-! ## Main results (copied from `TwistedParaproduct/Auto/Theorems.lean`) -/

namespace Auto

open MeasureTheory ENNReal SchwartzMap Topology Filter
open scoped ENNReal FourierTransform

/-- **Main Fourier estimate.** Let `d ≥ 2`, `1 < p < ∞` and `1 < qᵢ < ∞` with
`∑ 1/qᵢ = 1/p`. There is a constant `C > 0` such that for every multiplier `m` on
`ℝ^d` satisfying the Mikhlin condition of order `5d + 2` with constant `B ≥ 0`,
the twisted paraproduct `T_m` obeys `‖T_m(f₁,…,f_d)‖_p ≤ C B ∏ᵢ ‖fᵢ‖_{qᵢ}` for all
Schwartz functions `f₁,…,f_d`. -/
theorem main_result_fourier {d : ℕ} (hd : 2 ≤ d) {p : ℝ≥0∞} (hp : 1 < p ∧ p < ∞)
    {q : Fin d → ℝ≥0∞} (hq : ∀ i, 1 < q i ∧ q i < ∞)
    (hpq : ∑ i, (q i)⁻¹ = p⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ^d → ℂ) (B : ℝ), 0 ≤ B →
      MikhlinHormander.MikhlinCondition (5 * d + 2) m B →
      ∀ f : Fin d → 𝓢(ℝ^d, ℂ),
        eLpNorm (twisted m f) p ≤ ENNReal.ofReal (C * B) * ∏ i, eLpNorm (f i) (q i) :=
  sorry

/-- **Main theorem.** Let `d ≥ 2` and exponents as above. Let `K(y) = ‖y‖^{-d} Ω(y/‖y‖)`
be a homogeneous kernel that is smooth away from the origin and whose angular part
`Ω` has mean zero on the sphere. Then there is a multiplier `m` (the Fourier
transform of `K` as a principal-value distribution) and a constant `C ≥ 0` such
that for all Schwartz functions `f₁,…,f_d`: the truncations of the physical-space
operator over `ε < ‖y‖ < R` converge pointwise to `T_m(f₁,…,f_d)` as `ε → 0`,
`R → ∞`; the principal value `T_K` equals `T_m`; and
`‖T_K(f₁,…,f_d)‖_p ≤ C ∏ᵢ ‖fᵢ‖_{qᵢ}`. -/
theorem main_result {d : ℕ} (hd : 2 ≤ d) {p : ℝ≥0∞} (hp : 1 < p ∧ p < ∞)
    {q : Fin d → ℝ≥0∞} (hq : ∀ i, 1 < q i ∧ q i < ∞)
    (hpq : ∑ i, (q i)⁻¹ = p⁻¹)
    (Ω : Metric.sphere (0 : ℝ^d) 1 → ℂ)
    (hK : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (homogeneousKernel Ω) {y | y ≠ 0})
    (hΩ : (∫ ω, Ω ω ∂(volume : Measure (ℝ^d)).toSphere) = 0) :
    ∃ (m : ℝ^d → ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ g : 𝓢(ℝ^d, ℂ),
        (∫ y, compensatedPrincipalValue (homogeneousKernel Ω) g y) = ∫ ξ, m ξ * (𝓕⁻ g) ξ) ∧
      ∀ f : Fin d → 𝓢(ℝ^d, ℂ),
        (∀ x, Tendsto (fun a : ℝ × ℝ ↦ T_trunc (homogeneousKernel Ω) (fun i ↦ f i) x a.1 a.2)
          hardEndpointFilter (𝓝 (twisted m f x))) ∧
        T (homogeneousKernel Ω) (fun i ↦ f i) = twisted m f ∧
        eLpNorm (T (homogeneousKernel Ω) (fun i ↦ f i)) p ≤
          ENNReal.ofReal C * ∏ i, eLpNorm (f i) (q i) :=
  sorry

end Auto

end
