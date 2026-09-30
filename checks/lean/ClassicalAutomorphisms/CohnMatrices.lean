import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/- Cohn, printed pp. 33–34, (2.2), (2.5)–(2.8). E(x) is the
matrix [[x,1],[-1,0]] over an arbitrary associative ring with identity.
This verifies elementary relations used in the universal presentation,
not completeness of that presentation or the isomorphism classification. -/
namespace ClassicalAutomorphisms.Cohn

variable {R : Type*} [Ring R]

def E (x : R) : Matrix (Fin 2) (Fin 2) R := !![x, 1; -1, 0]

def Einv (x : R) : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, x]

theorem addition (x y : R) : E x * E 0 * E y = -E (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_two]

theorem square_zero : E (0 : R) * E 0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_two]

theorem cube_one : E (1 : R) * E 1 * E 1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_two]

theorem inverse_right (x : R) : E x * Einv x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Einv, Matrix.mul_apply, Fin.sum_univ_two]

theorem inverse_left (x : R) : Einv x * E x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Einv, Matrix.mul_apply, Fin.sum_univ_two]

theorem inverse_formula (x : R) : Einv x = E 0 * E (-x) * E 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Einv, Matrix.mul_apply, Fin.sum_univ_two]

theorem ternary (x y z : R) : E x * Einv y * E z = E (x - y + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Einv, Matrix.mul_apply, Fin.sum_univ_two]
  noncomm_ring

end ClassicalAutomorphisms.Cohn

#print axioms ClassicalAutomorphisms.Cohn.addition
#print axioms ClassicalAutomorphisms.Cohn.square_zero
#print axioms ClassicalAutomorphisms.Cohn.cube_one
#print axioms ClassicalAutomorphisms.Cohn.inverse_right
#print axioms ClassicalAutomorphisms.Cohn.inverse_left
#print axioms ClassicalAutomorphisms.Cohn.inverse_formula
#print axioms ClassicalAutomorphisms.Cohn.ternary
