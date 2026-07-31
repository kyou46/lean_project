import Mathlib

-- マルコフの不等式: ∀ ε > 0, P(X ≥ ε) ≤ E[X] / ε

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

example : P univ = 1 := by
  simp

#check (fun X : Ω → ℝ => P[X])

example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s

variable {X : Ω → ℝ} (hX : Measurable X)

theorem MarkovInequality {ε : ℝ} (hε : 0 < ε) (hX : Measurable X)
    (hXi : Integrable (fun ω => |X ω|) P) :
    P {ω | |X ω| ≥ ε } ≤ ENNReal.ofReal (P[fun ω => |X ω|] / ε) := by
    have h_pointwise : ∀ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ≤ |X ω| := by
        intro ω
        by_cases h : |X ω| ≥ ε
        · simp only [Set.indicator_of_mem (show ω ∈ {ω | |X ω| ≥ ε} from h), mul_one]
          exact h
        · simp only [Set.indicator_of_notMem (show ω ∉ {ω | |X ω| ≥ ε} from h), mul_zero]
          exact abs_nonneg _
    have h_meas : MeasurableSet {ω | ε ≤ |X ω|} :=
        measurableSet_le measurable_const hX.abs
    have h_integ : ∫ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P
        ≤ ∫ ω, |X ω| ∂P := by
        apply integral_mono
        · apply Integrable.const_mul
          rw [integrable_indicator_iff h_meas]
          exact (integrable_const 1).integrableOn
        · exact hXi
        · exact h_pointwise
    have h_final : ε * (P {ω | |X ω| ≥ ε}).toReal ≤ ∫ ω, |X ω| ∂P := by
        calc
            ε * (P {ω | |X ω| ≥ ε}).toReal
            = ε * ∫ ω, Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P := by
                congr 1
                exact (integral_indicator_one h_meas).symm
          _ = ∫ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P := by
                rw [integral_const_mul]
          _ ≤ ∫ ω, |X ω| ∂P := h_integ
    have h_div : (P {ω | ε ≤ |X ω|}).toReal ≤ (∫ ω, |X ω| ∂P) / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact h_final
    have h_enn := ENNReal.ofReal_le_ofReal h_div
    rw [ENNReal.ofReal_toReal (measure_ne_top P {ω | ε ≤ |X ω|})] at h_enn
    exact h_enn
