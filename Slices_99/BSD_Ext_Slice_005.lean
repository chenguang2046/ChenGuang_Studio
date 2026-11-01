import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
BSD_Ext_Slice_005 : Basic properties of the Dedekind eta function.

Uses mathlib's `ModularForm.eta_q` and the lemmas
`eta_q_eq_pow`, `eta_q_eq_cexp` and `eta_ne_zero`.
-/

open ModularForm Complex

namespace BSDExtSlice005

-- eta_q n z equals a power of exp(2*pi*i*z).
theorem eta_q_pow (n : ℕ) (z : ℂ) :
    eta_q n z = cexp (2 * Real.pi * I * z) ^ (n + 1) :=
  eta_q_eq_pow n z

-- eta_q n z in exponential form.
theorem eta_q_cexp (n : ℕ) (z : ℂ) :
    eta_q n z = cexp (2 * Real.pi * I * ((n : ℂ) + 1) * z) :=
  eta_q_eq_cexp n z

-- eta does not vanish on the upper half plane.
theorem eta_ne_zero_upper {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    η z ≠ 0 :=
  eta_ne_zero hz

end BSDExtSlice005


#print axioms BSDExtSlice005.eta_q_pow
#print axioms BSDExtSlice005.eta_q_cexp
#print axioms BSDExtSlice005.eta_ne_zero_upper
