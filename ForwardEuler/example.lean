import Mathlib.Analysis.ODE.Gronwall

instance : Module ℝ ℝ := {
  add_smul := fun r s x => by
    simp
    ring
  zero_smul := by
    simp
  mul_smul := fun r s x => by
    simp
    ring
  one_smul := by
    simp
  smul_zero := by
    simp
  smul_add := fun r x y => by
    simp
    ring
}

-- The Euler step for an ODE y' = v(t, y) with step size h is y_{n+1} = y_n + h * v(t_n, y_n).
def eulerStep {E : Type*} [AddCommGroup E] [Module ℝ E]
(v : ℝ → E → E) (h : ℝ) (t : ℝ) (y : E) : E :=
  y + h • v t y

def v' : ℝ → ℝ → ℝ := fun t y => y
#eval repr (eulerStep v' 1 0 1)

set_option trace.Meta.synthInstance true
#eval repr (eulerStep v' 1 0 1)

#check Real.normedField
#check NNReal.instModuleOfReal

example [Ring R] : Module R R := by infer_instance
example [Field R] : Module R R := by infer_instance
example : Module ℝ ℝ := by infer_instance

/--
The n-th point in the Euler method approximation with step size h.
-/
def eulerPoint {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℝ → E → E) (h : ℝ) (t0 : ℝ) (y0 : E) : ℕ → E
| 0 => y0
| n + 1 => eulerStep v h (t0 + n * h) (eulerPoint v h t0 y0 n)
