import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace ClassicalAutomorphisms

/-- The coordinate step in Ojanguren–Sridharan's proof after (15).
Cross-coordinate equalities plus a Bezout relation give proportionality;
no division by an individual coordinate is needed. -/
theorem coordinate_proportionality {R ι : Type*} [CommRing R] [Fintype ι]
    (a b k : ι → R) (hbezout : ∑ j, a j * k j = 1)
    (hcross : ∀ i j, b i * a j = b j * a i) (i : ι) :
    (∑ j, b j * k j) * a i = b i := by
  calc
    (∑ j, b j * k j) * a i = ∑ j, (b j * a i) * k j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, (b i * a j) * k j := by
      simp_rw [hcross]
    _ = b i * (∑ j, a j * k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = b i := by rw [hbezout, mul_one]

end ClassicalAutomorphisms

#print axioms ClassicalAutomorphisms.coordinate_proportionality
