import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Basic

/-!
# 仮想 Moore graph $(D=2,k=57)$: 基本パラメータと初期候補集合

対応するメモ: [`notes/moore-57/00-basic-facts.md`](../../notes/moore-57/00-basic-facts.md).

degree-diameter problem の未解決ケース $(D=2,k=57)$ に対応する仮想 Moore graph
$\Gamma$ の基本パラメータを Lean 上で扱うための土台を整備する。

## 数学的背景

そのような $\Gamma$ が存在するなら、Moore bound より頂点数は

$$
v=1+57+57\cdot 56=3250
$$

であり、strongly regular graph $(v,k,\lambda,\mu)=(3250,57,0,1)$ である。

自然言語メモ `00-basic-facts.md` では、自己同型群 $G$ の偶数位数候補について

* $|G|\le 110$ かつ $4\nmid|G|$ (既知結果)

を仮定している。これに対応する初期候補集合を `initialCandidates` として定義し、
$|G|$ が偶数なら `initialCandidates` に属するという主張を公理として受け入れる。

## このファイルの内容

* `SmallGraphs.Moore57.card_V` — 頂点数 $3250$.
* `SmallGraphs.Moore57.IsMoore57` — `IsSRGWith 3250 57 0 1` の略記。
* `SmallGraphs.Moore57.isoEquivSubtype`, `SmallGraphs.Moore57.fintypeIso` —
  抽象的な単純グラフ `G : SimpleGraph V` の自己同型群 `G ≃g G` を `Fintype` として
  扱うための補助構成。
* `SmallGraphs.Moore57.initialCandidates` — 自己同型群の初期偶数位数候補集合
  $\{2,6,10,\dots,110\}$.
* `SmallGraphs.Moore57.aut_card_in_initialCandidates` —
  $|G|$ が偶数なら `initialCandidates` に属する、という主張を公理として受け入れる。
-/

namespace SmallGraphs.Moore57

open SimpleGraph

/-! ### 基本パラメータ -/

/-- $(D=2,k=57)$ の Moore graph の頂点数 $1+57+57\cdot 56=3250$. -/
abbrev card_V : ℕ := 3250

/-! ### 仮想 Moore graph の定義

`SimpleGraph.IsSRGWith 3250 57 0 1` をそのまま使う。これは

* 頂点数 $|V|=3250$,
* $57$-正則,
* 隣接二頂点の共通隣接点数が $0$ ($\lambda=0$, 三角形なし),
* 異なる非隣接二頂点の共通隣接点数が $1$ ($\mu=1$),

の組合せである。Moore graph $(D=2,k=57)$ は strongly regular graph
$(3250,57,0,1)$ と同値であることに注意する。 -/
abbrev IsMoore57 {V : Type*} [Fintype V] (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] : Prop :=
  Γ.IsSRGWith card_V 57 0 1

/-! ### 自己同型群を Fintype として扱うための一般的な構成

`G ≃g G` を `Equiv.Perm V` の subtype と同値で対応させ、`Fintype` 構造を移植する。
具体的なグラフ用の同様の構成は `SmallGraphs.M8.isoEquivSubtype` および
`SmallGraphs.K33Exp.isoEquivSubtype` にあるが、ここでは抽象的な形で再構成する。 -/

/-- グラフ自己同型 `G ≃g G` と「隣接を保つ全単射」の subtype の同値。 -/
def isoEquivSubtype {V : Type*} (G : SimpleGraph V) :
    { f : V ≃ V // ∀ a b, G.Adj a b ↔ G.Adj (f a) (f b) } ≃ (G ≃g G) where
  toFun := fun ⟨e, h⟩ =>
    { toEquiv := e
      map_rel_iff' := fun {a b} => (h a b).symm }
  invFun := fun f => ⟨f.toEquiv, fun _ _ => f.map_rel_iff'.symm⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- 任意の `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]` の下で `G ≃g G` は Fintype.

具体的なグラフ (例: `SmallGraphs.M8.graph`) には個別の Fintype 実装があるため、
そちらを優先するように低い優先度を指定している。 -/
instance (priority := 100) fintypeIso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (G ≃g G) :=
  Fintype.ofEquiv _ (isoEquivSubtype G)

/-! ### 初期偶数位数候補集合 -/

/-- 自己同型群の初期偶数位数候補集合
$\{2,6,10,14,18,22,26,30,34,38,42,46,50,54,58,62,66,70,74,78,82,86,90,94,98,102,106,110\}$.

これは $0<n\le 110$ かつ $n\equiv 2\pmod 4$ なる $n$ 全体である。 -/
def initialCandidates : Finset ℕ :=
  (Finset.range 28).image (fun i => 4 * i + 2)

theorem card_initialCandidates : initialCandidates.card = 28 := by decide

/-! ### 自己同型群位数の初期候補性 (公理として受け入れる)

仮想 Moore graph $\Gamma$ の自己同型群 $G$ の位数が偶数なら、$|G|$ は
`initialCandidates` に属するという主張をここでは公理として受け入れる。

具体的には、既知結果 ($|G|$ 偶数なら $|G|\le 110$ かつ $4\nmid|G|$) に基づく
ものであり、本リポジトリでは現時点で形式的証明を与えていない。 -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、それは
`initialCandidates` に属する。

既知結果に基づく主張であり、ここでは形式的証明を与えず公理として受け入れる。 -/
axiom aut_card_in_initialCandidates
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    Fintype.card (Γ ≃g Γ) ∈ initialCandidates

end SmallGraphs.Moore57
