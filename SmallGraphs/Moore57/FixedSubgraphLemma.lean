import SmallGraphs.Moore57.BasicFacts

/-!
# 仮想 Moore graph $(D=2,k=57)$: 固定点部分グラフ補題

対応するメモ:
[`notes/moore-57/01-fixed-subgraph-lemma.md`](../../notes/moore-57/01-fixed-subgraph-lemma.md).

素数位数の自己同型 $g\in\operatorname{Aut}(\Gamma)$ について、
固定点集合 $F=\operatorname{Fix}(g)$ 上の誘導部分グラフ $H=\Gamma[F]$ の
構造に関する補題群を扱う。

## 主な主張 (現時点では未形式化)

任意の素数 $p$ と $g$ が位数 $p$ の自己同型のとき、$F=\operatorname{Fix}(g)$,
$H=\Gamma[F]$ について次が成り立つ。

* 次数合同条件: 任意の $x\in F$ について $d_H(x)\equiv 57\pmod p$.
* 和公式: 任意の $x\in F$ について $\sum_{y\sim_H x} d_H(y)=|F|-1$.
* 固定点部分グラフの構造: $H$ は

  - 正則グラフ (もし完全に固定なら $\Gamma$ 全体), または
  - 星型 $K_{1,m}$ (非正則の場合)

  に限られる。

## 形式化の現状

未形式化。ここでは骨組みのみを置き、後続のメモ (`02`–`04`) で参照されるため
の名前空間を確保する。
-/

namespace SmallGraphs.Moore57

-- 固定点部分グラフ補題の Lean 化は今後の課題。

end SmallGraphs.Moore57
