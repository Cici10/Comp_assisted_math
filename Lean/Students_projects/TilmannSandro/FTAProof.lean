import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.IsAlgClosed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Algebra.Module.LinearMap
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
open Matrix
open Fintype


variable {m : ℕ} [Fintype (Fin m)] [Field ℂ]

def IsEigenvector (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) := (v ≠ 0) ∧ (∃ μ : ℂ, (mulVec A v) = μ • v)

theorem exists_eigenvector (A : Matrix (Fin m) (Fin m) ℂ) : (m ≥ 1) → (∃ v : Fin m → ℂ, IsEigenvector A v) :=
by sorry


/- def IsEigenvector [Fintype n] [Field ℂ] (A : Matrix n n ℂ)  (v : n → ℂ) := (v ≠ 0 ) ∧ (∃ μ : ℂ ,  (mulVec A v = μ • v ))


theorem exists_eigenvector [Fintype n] [Field ℂ] (A : Matrix n n ℂ) : (card n ≥ 1) → (∃ v : n → ℂ,
 IsEigenvector  A v) := by sorry -/


 
 /-odd dimensinal case-/
 theorem exists_eigenvector_odd (A : Matrix (Fin m) (Fin m) ℂ): (Odd (card)) → (∃ v :  Fin m → ℂ,
 IsEigenvector  A v) := by sorry
 
 /-Lemma 3-/
 open FiniteDimensional
 open LinearMap
 open Module
 universe u v w

 variable {ℂ : Type v} {V : Type w} [Field ℂ] [AddCommGroup V] [Module ℂ V]


 lemma comm_lin_opHasEigenvector [FiniteDimensional ℂ V] [Nontrivial V] (f : End ℂ V) (g : End ℂ V) (h : End ℂ V) 
 : (m ≥ 1) ∧ ¬(m ∣ (finrank ℂ  V))∧ (∃ v : V , f.HasEigenvector μ v)→ (∃ v : V , g.HasEigenvector μ v ∧ h.HasEigenvector ν v)  := sorry

