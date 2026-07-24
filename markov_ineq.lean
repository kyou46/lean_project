import Mathlib

/-!
# マルコフ不等式 (Markov's Inequality) の形式化 — サンプル

確率空間 `(Ω, ℱ, μ)` 上の非負値関数 `X : Ω → ℝ≥0∞` と定数 `a` に対して，
`a * μ {ω | a ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ`
が成り立つ，という主張を形式化する．

## 証明のアイデア
1. `s := {ω | a ≤ X ω}` とおく．
2. 「`s` 上で `a`，`s` の外で `0`」という指示関数 `s.indicator (fun _ => a)` は，
   任意の `ω` について `X ω` 以下である（`s` の定義そのものから従う）．
3. 両辺を積分すると，左辺は `lintegral_indicator_const` により `a * μ s` に等しく，
   右辺は単調性 `lintegral_mono` によって `∫⁻ ω, X ω ∂μ` 以下になる．
-/

open MeasureTheory ENNReal Set

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **マルコフ不等式**（`ℝ≥0∞` 値・Lebesgue 積分版）．
`X` が可測かつ非負（`ℝ≥0∞` 値なので自動的に非負）ならば，
任意の `a : ℝ≥0∞` に対して `a * μ {ω | a ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ` が成り立つ． -/
theorem markov_inequality
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (a : ℝ≥0∞) :
    a * μ {ω | a ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ := by
  -- 集合の可測性
  have hs : MeasurableSet {ω | a ≤ X ω} := hX measurableSet_Ici
  -- 指示関数 ≤ X を点ごとに示す
  have key : (fun ω => {ω | a ≤ X ω}.indicator (fun _ => a) ω) ≤ X := by
    intro ω
    dsimp
    rw [Set.indicator_apply]
    split_ifs with h
    · exact h
    · exact zero_le
  -- 指示関数の積分で挟む
  have h_eq : a * μ {ω | a ≤ X ω} = ∫⁻ ω, {ω | a ≤ X ω}.indicator (fun _ => a) ω ∂μ := by
    rw [lintegral_indicator_const hs]
  have h_le : (∫⁻ ω, {ω | a ≤ X ω}.indicator (fun _ => a) ω ∂μ) ≤ ∫⁻ ω, X ω ∂μ := by
    exact lintegral_mono key
  -- 結合して証明完了
  exact h_eq.trans_le h_le
/-!
## 補足：実数値・古典的な形への拡張（発展課題）

上の定理は「拡張実数値の確率変数」に対する一般的な形．
より馴染みのある古典的な形

`P(X ≥ a) ≤ E[X] / a`  (`X : Ω → ℝ`, `X ≥ 0` a.e., `X` 可積分, `a > 0`)

は，`ENNReal.ofReal` を介して `markov_inequality` を適用し，
`Integrable` から得られる `∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ENNReal.ofReal (∫ ω, X ω ∂μ)`
（`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` 等）を使って変換すれば得られる．
これは自分で仕上げてみると，形式化の「面白さ」を語るドキュメントのネタとしても良い．
-/
