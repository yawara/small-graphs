import SmallGraphs.Moore57.CompositeOrderObstructions

/-!
# 仮想 Moore graph $(D=2,k=57)$: 位数 $70$ の解析

対応するメモ:
[`notes/moore-57/04-order-70-analysis.md`](../../notes/moore-57/04-order-70-analysis.md).

候補位数 $|G|=70$ は現時点では完全には排除できていないが、残るなら群構造は

$$
G\cong C_5\times D_{14}
$$

に限られる、ということを示す。さらに、$N=C_{35}$-軌道分解
$1+10\cdot 5+7\cdot 7+90\cdot 35=3250$ と商行列の強い制約を満たす必要がある。

## 主な主張 (現時点では未形式化)

* $|G|=70$ なら $G\cong C_5\times D_{14}$.
* この型では involution は $C_5$ を中心化し、$C_7$ を反転する。
* $\operatorname{Fix}(C_5)$ は Hoffman--Singleton graph に同型である。
* $\operatorname{Fix}(C_7)\cong K_{1,50}$ である。
* $C_{35}$-軌道分解は $1+10\cdot 5+7\cdot 7+90\cdot 35$ である。

## 形式化の現状

未形式化。位数 $70$ は `remainingCandidates` の中に残ったまま、
さらなる解析を要する。
-/

namespace SmallGraphs.Moore57

-- 位数 70 の解析の Lean 化は今後の課題。

end SmallGraphs.Moore57
