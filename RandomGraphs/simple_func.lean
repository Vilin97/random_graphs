import Mathlib.MeasureTheory.Function.SimpleFunc

open MeasureTheory BigOperators

namespace SimpleFunc
variable {ι α β : Type*} [MeasurableSpace α] [CommMonoid β]

-- lemma by Yael Dillies, from Zulip
@[to_additive (attr := simp, norm_cast)]
lemma coe_prod (f : ι → SimpleFunc α β) (s : Finset ι)  : ∏ i in s, f i = ∏ i in s, ⇑(f i) := by
  induction s using Finset.cons_induction <;> simp [*]

lemma coe_sum' (f : I → SimpleFunc α ℝ) [Fintype I] : ∑ i, f i = ∑ i, ⇑(f i) := by
  simp only [coe_sum]
