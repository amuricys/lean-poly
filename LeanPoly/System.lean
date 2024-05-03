import Init.Prelude
import LeanPoly.Data

import SciLean
import SciLean.Core.Approx.ApproxLimit
import SciLean.Core.Notation.Gradient
-- import SciLean.Tactic.LetNormalize
-- import SciLean.Tactic.PullLimitOut
import SciLean.Modules.DifferentialEquations

-- set_default_scalar Float

-- open SciLean

namespace CategoryTheory
namespace Poly
namespace hide

structure DynamicalSystem : Type _ where
  state : Type
  interface : Poly
  dynamics : state y^state ⟶ interface

def parallel (ds1 ds2 : DynamicalSystem) : DynamicalSystem :=
  { state := ds1.state × ds2.state,
    interface := ds1.interface ⊗ ds2.interface,
    -- TODO: How to hide SciLean's ⊗ notation?
    dynamics := tensor.map _ _ _ _ ds1.dynamics ds2.dynamics }


/-
Continuous Part:

Let T(t) be the room temperature at time t.

We can model the heat transfer with a simple first-order differential equation:

dT(t)/dt = -k(T(t) - T_a)

where:
* k is a positive constant representing the heat loss rate (k > 0).
* T_a is the ambient temperature (constant).

Discrete Part:

The thermostat has two discrete states:
ON (H) - Heater is active.
OFF (L) - Heater is inactive.
Two threshold temperatures define the hysteresis:
T_on (upper threshold) - Heater turns on when T(t) falls below this.
T_off (lower threshold) - Heater turns off when T(t) reaches this.
-/

def continuous : DynamicalSystem :=
  { state := ℝ,
    interface := Poly.scalar ℝ,
    dynamics := λ T, -k * (T - T_a) }



end hide
end Poly
end CategoryTheory
