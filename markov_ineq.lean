import Mathlib

-- マルコフの不等式: ∀ ε > 0, P(X ≥ ε) ≤ E[X] / ε

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

#check (fun X : Ω → ℝ => P[X]) -- 期待値の書き方を確認

variable {X : Ω → ℝ} (hX : Measurable X)

theorem MarkovInequality {ε : ℝ} (hε : 0 < ε) (hX : Measurable X)
    (hXi : Integrable (fun ω => X ω) P) :
    P {ω | |X ω| ≥ ε } ≤ ENNReal.ofReal (P[fun ω => |X ω|] / ε) := by
    -- 指示関数で下界を与える
    have h_pointwise : ∀ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ≤ |X ω| := by
        intro ω
        by_cases h : |X ω| ≥ ε
        · simp only [Set.indicator_of_mem (show ω ∈ {ω | |X ω| ≥ ε} from h), mul_one]
          exact h
        · simp only [Set.indicator_of_notMem (show ω ∉ {ω | |X ω| ≥ ε} from h), mul_zero]
          exact abs_nonneg _
    -- 確率変数の絶対値の可測性
    have h_meas : MeasurableSet {ω | ε ≤ |X ω|} :=
        measurableSet_le measurable_const hX.abs
    -- 指示関数と |X| の大小関係から積分の単調性によって積分の大小関係を導く
    have h_integ : ∫ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P
        ≤ ∫ ω, |X ω| ∂P := by
        apply integral_mono
        · apply Integrable.const_mul
          rw [integrable_indicator_iff h_meas]
          exact (integrable_const 1).integrableOn
        · exact hXi.abs
        · exact h_pointwise
    -- 確率の言語に戻す
    have h_final : ε * (P {ω | |X ω| ≥ ε}).toReal ≤ ∫ ω, |X ω| ∂P := by
        calc
            ε * (P {ω | |X ω| ≥ ε}).toReal
            = ε * ∫ ω, Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P := by
                congr 1
                exact (integral_indicator_one h_meas).symm
          _ = ∫ ω, ε * Set.indicator {ω | |X ω| ≥ ε} (fun _ => (1 : ℝ)) ω ∂P := by
                rw [integral_const_mul]
          _ ≤ ∫ ω, |X ω| ∂P := h_integ
    -- 両辺を ε で割る
    have h_div : (P {ω | ε ≤ |X ω|}).toReal ≤ (∫ ω, |X ω| ∂P) / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact h_final
    -- ENNReal 上の不等式に書き換える
    have h_enn := ENNReal.ofReal_le_ofReal h_div
    rw [ENNReal.ofReal_toReal (measure_ne_top P {ω | ε ≤ |X ω|})] at h_enn
    exact h_enn

-- チェビシェフの不等式: ∀ ε > 0, P(|X - E[X]| ≥ ε) ≤ Var(X) / ε^2

theorem ChebyshevInequality {ε : ℝ} (hε : 0 < ε) (hX : Measurable X)
    (hXi : Integrable (fun ω => X ω) P) (hXsqi : Integrable (fun ω => (X ω) ^ 2) P) :
    P {ω | |X ω - P[X]| ≥ ε} ≤ ENNReal.ofReal (variance X P / ε^2) := by
    -- ε^2 が正であること
    have hε2 : 0 < ε^2 := sq_pos_of_ne_zero (ne_of_gt hε)
    -- {ω | |X ω - P[X]| ≥ ε} と {ω | (X ω - P[X]) ^ 2 ≥ ε^2} が集合として同じ
    have h_set : {ω | |X ω - P[X]| ≥ ε} = {ω | (X ω - P[X]) ^ 2 ≥ ε^2}
    := by
        ext ω
        simp only [Set.mem_setOf_eq]
        have hε_abs : |ε| = ε := abs_of_pos hε
        rw [← hε_abs]
        nth_rw 1 [← hε_abs] -- 下の引数指定ができるようにさらに rewrite
        exact (sq_le_sq (a := |ε|) (b := X ω - P[X])).symm
    rw [h_set]
    -- (X - E[X]) ^ 2 が可積分であること
    have hY: Integrable (fun ω => (X ω - P[X]) ^ 2) P := by
        have h_eq : (fun ω => (X ω - P[X]) ^ 2) = (fun ω => X ω ^ 2 - 2 * P[X] * X ω + P[X] ^ 2)
        := by ext ω; ring
        rw [h_eq]
        refine ((hXsqi.sub (hXi.const_mul (2 * P[X]))).add (integrable_const (P[X] ^ 2)))
    -- Y の可測性
    have hY_meas : Measurable (fun ω => (X ω - P[X]) ^ 2) :=
        (hX.sub_const P[X]).pow_const 2
    -- マルコフの不等式を適用
    have h_markov := MarkovInequality hε2 hY_meas hY
    -- 絶対値を外す
    have h_abs : (fun ω => |(X ω - P[X]) ^ 2|) = (fun ω => (X ω - P[X]) ^ 2) := by
        ext ω
        exact abs_of_nonneg (sq_nonneg _)
    rw [h_abs] at h_markov
    -- 絶対値を外しても集合として同じであること
    have h_abs_set : {ω | |(X ω - P[X]) ^ 2| ≥ ε ^ 2} = {ω | (X ω - P[X]) ^ 2 ≥ ε ^ 2} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [abs_of_nonneg (sq_nonneg _)]
    rw [h_abs_set] at h_markov
    -- 分散の定義を展開する
    have h_var : ∫ ω, (X ω - ∫ x, X x ∂P) ^ 2 ∂P = eVar[X; P].toReal := by
      exact (variance_eq_integral hX.aemeasurable).symm
    rw [h_var] at h_markov
    -- 上のことを合わせて Chebyshev の不等式の形にできる
    exact h_markov
