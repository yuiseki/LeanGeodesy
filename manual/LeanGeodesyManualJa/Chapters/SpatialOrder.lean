import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "部分木は整数の区間になる" =>
%%%
file := "spatial-order"
tag := "ja-spatial-order"
%%%

あるタイルの内側にある、より細かいズームのタイルをすべて取り出したいとします。たとえば、ズーム 10 のあるタイルに含まれるズーム 14 のタイルを、データベースから一度に検索したい場面です。タイルを一つずつ列挙するのではなく、「番号が $`a` 以上 $`b` 以下」という一回の範囲検索で済ませることはできるのでしょうか。

前の二章で見た Morton 順序と Hilbert 順序は、並べ方こそ違いますが、「番号を 4 で割ると親の番号になる」という性質を共有していました。この章では、この性質を持つ並べ方を空間順序と呼び、この性質だけから範囲検索の答えを導きます。

```
番号を 4 で割ると親の番号（空間順序）
  ↓
k 世代上の祖先の番号は、番号を 4^k で割ったもの
  ↓
子孫であることは、番号が一つの区間に入ること
  ↓
部分木 = 整数の一つの区間
```

# 空間順序とは
%%%
tag := "t-spatial-order"
%%%

空間順序とは、各ズーム $`z` のタイルに $`0`〜$`4^z - 1` の番号を一対一に割り当てる方法のうち、親の番号がいつも子の番号を 4 で割ったものになっているものです。

{leanDecl Geodesy.Tiles.SpatialOrder}

Morton 順序も Hilbert 順序も、この意味での空間順序です。

{leanDecl Geodesy.Tiles.mortonOrder}

{leanDecl Geodesy.Tiles.hilbertOrder}

# 一つの性質から範囲検索へ
%%%
tag := "t-interval"
%%%

親の番号が 4 で割った値なら、$`k` 世代上の祖先の番号は $`4^k` で割った値です。割り算を $`k` 回繰り返すだけです。

{leanDecl Geodesy.Tiles.SpatialOrder.index_ancestor}

すると、タイル $`t` がタイル $`s` の $`k` 世代下の子孫であることは、$`t` の番号を $`4^k` で割ると $`s` の番号になること、すなわち

$$`\text{index}(s) \cdot 4^k \le \text{index}(t) < (\text{index}(s) + 1) \cdot 4^k`

と同じです。

{leanDecl Geodesy.Tiles.SpatialOrder.ancestor_eq_iff_mem_interval}

したがって、あるタイルの $`k` 世代下の子孫全体は、番号の一つの区間にぴったり一致します。区間の外に子孫はなく、区間の中に子孫でないタイルはありません。

{leanDecl Geodesy.Tiles.SpatialOrder.subtree_eq_symm_interval}

冒頭の問いの答えは「できる」です。ズーム 10 のタイル $`s` に含まれるズーム 14 のタイルは、空間順序の番号で `index(s) * 256` 以上 `(index(s) + 1) * 256` 未満のものです。Morton でも Hilbert でも同じ式で、どちらを使っても、部分木の検索はインデックス上の一回の範囲走査になります。

この結果が一般の空間順序について証明されていることにも意味があります。Morton と Hilbert の二つの場合を別々に確かめたのではなく、「番号を 4 で割ると親の番号」という性質さえ満たせば、どんな並べ方でも部分木は区間になるのです。

# 違いは隣接だけ
%%%
tag := "t-adjacency"
%%%

部分木が区間になる点で、Morton と Hilbert に違いはありません。二つを分けるのは、番号が一つ違うタイルが地図の上で隣り合うかどうかです。これを空間順序の性質として定義すると、

{leanDecl Geodesy.Tiles.SpatialOrder.IsAdjacentOrder}

Hilbert 順序はこの性質を持ち、Morton 順序は持ちません。

{leanDecl Geodesy.Tiles.hilbertOrder_isAdjacentOrder}

{leanDecl Geodesy.Tiles.mortonOrder_not_isAdjacentOrder}

実装での使い分けもここから見えてきます。部分木の検索だけが目的なら、計算が単純な Morton 符号で十分です。地図の上で近いタイルが番号の上でも近いことが効く場面、たとえば連続した範囲を読むときにディスク上の局所性を高めたい場合には、Hilbert 順序が有利です。ただし Hilbert でも、地図上で隣り合う二枚のタイルが番号の上で近いとは限りません。保証されているのは、番号が隣なら地図でも隣、という向きだけです。

# 第II部のまとめと次へ
%%%
tag := "t-part-summary"
%%%

第II部では、Web Mercator の正方形の世界をタイルに切り（2.1 章）、タイルが四分木をなすことを見て（2.2 章）、それを一列に並べる二つの方法、Morton（2.3 章）と Hilbert（2.4 章）を比べました。二つは同じ空間順序の仲間で、部分木が整数の区間になるという、空間インデックスにとって最も大事な性質を共有しています。違いは隣接性だけです（2.5 章）。

ここまでで、地球の形、地図投影、タイルを見てきました。ところで、GIS で座標を扱うときに必ず出てくる EPSG:4326 や EPSG:3857 というコードは、この本のどこに当たるのでしょうか。第III部では、座標参照系を、ここまで組み立ててきた数学の上に置き直します。
