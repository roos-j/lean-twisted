/-
Copyright (c) 2026 Polona Durcik, Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file was assembled by Claude from the statement files
`TwistedParaproduct/Auto/Defs.lean` and `TwistedParaproduct/Auto/Theorems.lean`
(whose statements were checked against the manuscript by the author), together
with the Mikhlin condition from `LeanSpherical/Auto/MikhlinHormander.lean` in the
`lean-spherical` dependency.
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

namespace Auto.Spherical.SurfaceMeasureDecay

/-- Euclidean space `ℝ^d`. -/
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

end Auto.Spherical.SurfaceMeasureDecay

namespace Auto.MikhlinHormander

open Auto.Spherical.SurfaceMeasureDecay

/-- Derivative bounds `‖ξ‖^k ‖D^k m(ξ)‖ ≤ C` for all `k ≤ N` and `ξ ≠ 0`. -/
@[expose] def aux_MikhlinCondition {d : Nat} (N : Nat) (m : Euclidean d → Complex)
    (C : Real) : Prop :=
  ∀ k ≤ N, ∀ ξ : Euclidean d, ξ ≠ 0 →
    ‖ξ‖ ^ k * ‖iteratedFDeriv Real k m ξ‖ ≤ C

/-- Mikhlin condition: `m` is `C^N` away from `0` and satisfies the derivative bounds. -/
@[expose] def MikhlinCondition {d : Nat} (N : Nat) (m : Euclidean d → Complex)
    (C : Real) : Prop :=
  ContDiffOn Real N m ({0}ᶜ : Set (Euclidean d)) ∧
  aux_MikhlinCondition N m C

end Auto.MikhlinHormander

namespace Auto

-- Match the instance context of `Defs.lean`.
attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Filter Topology Set SchwartzMap
open scoped BigOperators FourierTransform

/-- Euclidean space `ℝ^n`. -/
scoped notation:max "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

/-- The `i`th standard unit vector `eᵢ`. -/
@[expose] noncomputable abbrev unitVector {d : ℕ} (i : Fin d) : ℝ^d :=
  EuclideanSpace.single i (1 : ℝ)

/-- The diagonal frequency `(ξ₁₁, …, ξ_dd)`: coordinate `j` of the `j`th frequency. -/
@[expose] def diagonalFrequency {d : ℕ} (ξ : Fin d → ℝ^d) : ℝ^d :=
  WithLp.toLp 2 (fun j => ξ j j)

/-- The integrand of the twisted paraproduct `twisted`. -/
@[expose] noncomputable def fourierIntegrand {d : ℕ} (m : ℝ^d → ℂ)
    (f : Fin d → 𝓢(ℝ^d, ℂ)) (x : ℝ^d) (ξ : Fin d → ℝ^d) : ℂ :=
  m (diagonalFrequency ξ) * (∏ j, (𝓕 (f j)) (ξ j)) *
    Complex.exp (Complex.I * Complex.ofReal
      (2 * Real.pi * inner ℝ x (∑ j, ξ j)))

/-- The twisted paraproduct `T_m(f)(x) = ∫ m(ξ₁₁, …, ξ_dd) ∏ᵢ f̂ᵢ(ξᵢ) e^{2πi x·∑ξᵢ} dξ`. -/
@[expose] noncomputable def twisted {d : ℕ} (m : ℝ^d → ℂ)
    (f : Fin d → 𝓢(ℝ^d, ℂ)) (x : ℝ^d) : ℂ :=
  ∫ ξ : Fin d → ℝ^d,
    m (diagonalFrequency ξ) * (∏ i, (𝓕 (f i)) (ξ i)) *
      Complex.exp (Complex.I * Complex.ofReal (2 * Real.pi * inner ℝ x (∑ i, ξ i)))

/-- The physical-space operator `∫ L(y) ∏ᵢ fᵢ(x - yᵢ eᵢ) dy` with kernel `L`. -/
@[expose] noncomputable def physicalKernelApply {d : ℕ} (L : ℝ^d → ℂ)
    (f : Fin d → ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  ∫ y, L y * ∏ i, f i (x - y i • unitVector i)

/-- The kernel `K` restricted to the annulus `ε < ‖x‖ < R`. -/
@[expose] noncomputable def hardAnnulus {d : ℕ} (K : ℝ^d → ℂ) (ε R : ℝ) : ℝ^d → ℂ :=
  {x : ℝ^d | ε < ‖x‖ ∧ ‖x‖ < R}.indicator K

/-- The homogeneous kernel `K(y) = ‖y‖^{-d} Ω(y/‖y‖)`, with `K(0) = 0`. -/
@[expose] noncomputable def homogeneousKernel {d : ℕ}
    (Ω : Metric.sphere (0 : ℝ^d) 1 → ℂ) (y : ℝ^d) : ℂ :=
  if hy : y = 0 then 0 else
    (↑(‖y‖⁻¹^d):ℂ) * Ω ((homeomorphUnitSphereProd (ℝ^d) ⟨y,hy⟩).1)

/-- The integrand `K(y) (g(y) - 1_{‖y‖ ≤ 1} g(0))` of the principal-value pairing. -/
@[expose] noncomputable def compensatedPrincipalValue {d : ℕ} (K g : ℝ^d → ℂ)
    (y : ℝ^d) : ℂ :=
  K y * (g y - {z : ℝ^d | ‖z‖ ≤ 1}.indicator (fun _ => g 0) y)

/-- The limit `ε → 0⁺, R → ∞` on pairs `(ε, R)`. -/
@[expose] noncomputable def hardEndpointFilter : Filter (ℝ × ℝ) :=
  (𝓝[>] (0:ℝ)) ×ˢ atTop

/-- The operator with kernel `K` truncated to `ε < ‖y‖ < R`. -/
@[expose] noncomputable def T_trunc {d : ℕ} (K : ℝ^d → ℂ) (f : Fin d → ℝ^d → ℂ)
    (x : ℝ^d) (ε R : ℝ) : ℂ :=
  physicalKernelApply (hardAnnulus K ε R) f x

/-- The principal value `T_K`: the limit of the truncations as `ε → 0⁺, R → ∞`. -/
@[expose] noncomputable def T {d : ℕ} (K : ℝ^d → ℂ) (f : Fin d → ℝ^d → ℂ) (x : ℝ^d) : ℂ :=
  limUnder hardEndpointFilter (fun a : ℝ × ℝ ↦ T_trunc K f x a.1 a.2)

end Auto

namespace Auto

open MeasureTheory ENNReal SchwartzMap Topology Filter
open scoped ENNReal FourierTransform

/-- **Main Fourier theorem.** For `d ≥ 2` and Hölder exponents in the full open Banach range,
every multiplier `m` with Mikhlin constant `B` satisfies `‖T_m(f)‖_p ≤ C B ∏ᵢ ‖fᵢ‖_{qᵢ}`
on Schwartz functions. -/
theorem main_result_fourier {d : ℕ} (hd : 2 ≤ d) {p : ℝ≥0∞} (hp : 1 < p ∧ p < ∞)
    {q : Fin d → ℝ≥0∞} (hq : ∀ i, 1 < q i ∧ q i < ∞)
    (hpq : ∑ i, (q i)⁻¹ = p⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ^d → ℂ) (B : ℝ), 0 ≤ B →
      MikhlinHormander.MikhlinCondition (5 * d + 2) m B →
      ∀ f : Fin d → 𝓢(ℝ^d, ℂ),
        eLpNorm (twisted m f) p ≤ ENNReal.ofReal (C * B) * ∏ i, eLpNorm (f i) (q i) :=
  sorry

/-- **Main homogeneous theorem.** For `d ≥ 2`, Hölder exponents in the full open Banach range, and a smooth homogeneous kernel `K` with mean-zero `Ω`, the principal value `T_K` exists, equals
`T_m` with `m = K̂`, and `‖T_K(f)‖_p ≤ C ∏ᵢ ‖fᵢ‖_{qᵢ}`. -/
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
