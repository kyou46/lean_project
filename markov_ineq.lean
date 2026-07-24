import Mathlib.MeasureTheory.Integral.Lebesgue

open MeasureTheory ENNReal Set

/--
マルコフの不等式 (Markov's Inequality)
測度空間上の非負値可測関数 $f$ と定数 $a \ge 0$ に対して、
$a \cdot \mu(\{x \mid a \le f(x)\}) \le \int f d\mu$ が成立する。
-/
theorem markov_inequality
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) :
    a * μ {x | a ≤ f x} ≤ ∫⁻ x, f x ∂μ := by
  -- Mathlibに証明済みのルベーグ積分に関する基本不等式を直接適用する
  exact mul_meas_ge_le_lintegral hf a

/--
少し変形したバージョン（右辺への移行）
-/
theorem markov_inequality_variant
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) :
    μ {x | a ≤ f x} ≤ (∫⁻ x, f x ∂μ) / a := by
  -- a * μ(E) ≤ ∫ f から μ(E) ≤ (∫ f) / a を導出する
  apply ENNReal.le_div_of_mul_le
  -- 左辺の条件は先ほど証明したマルコフの不等式と一致する
  exact markov_inequality f hf a
