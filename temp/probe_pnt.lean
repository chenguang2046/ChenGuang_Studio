import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Filter Asymptotics

#check Chebyshev.isBigO_psi_sub_theta_sqrt
#check sqrt
#check Real.sqrt
#check IsBigO atTop (Chebyshev.psi - Chebyshev.theta : ℝ → ℝ) (Real.sqrt)
#check Chebyshev.psi
#check Chebyshev.theta
#check Chebyshev.psi - Chebyshev.theta
