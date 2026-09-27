import VersoManual
import LeanGeodesyManualJa.Chapters.TileGrid
import LeanGeodesyManualJa.Chapters.Quadtree
import LeanGeodesyManualJa.Chapters.Morton
import LeanGeodesyManualJa.Chapters.Hilbert
import LeanGeodesyManualJa.Chapters.SpatialOrder

open Verso.Genre Manual

#doc (Manual) "第II部 Web 地図のタイル番号にある数学" =>
%%%
file := "part2"
tag := "ja-part2"
%%%

Web 地図は、第I部の Web Mercator が描いた正方形の世界を、ズームレベルごとに正方形のタイルに切って配信しています。タイルには $`(z, x, y)` の番号が付き、quadkey や Morton 符号、Hilbert 番号といった別の名前でも呼ばれます。第II部では、これらの番号がどんな数学的構造を持ち、実装で何を保証してくれるのかを見ます。

```
Web Mercator の正方形
  ↓
タイルの格子
  ↓
四分木
  ↓
Morton 順序 ／ Hilbert 順序
  ↓
空間順序：部分木 = 整数の一つの区間
```

最初の 2.1 章だけが地図と数を結ぶ章で、2.2 章から先は整数だけの話になります。緯度経度も三角関数も出てきません。

{include 1 LeanGeodesyManualJa.Chapters.TileGrid}
{include 1 LeanGeodesyManualJa.Chapters.Quadtree}
{include 1 LeanGeodesyManualJa.Chapters.Morton}
{include 1 LeanGeodesyManualJa.Chapters.Hilbert}
{include 1 LeanGeodesyManualJa.Chapters.SpatialOrder}
