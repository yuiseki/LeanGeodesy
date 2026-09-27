import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "正方形の世界をタイルに切る" =>
%%%
file := "tile-grid"
tag := "ja-tile-grid"
%%%

Web 地図のタイルの URL には `/{z}/{x}/{y}.png` のような三つの数が入っています。ある地点の緯度経度から、この $`x` と $`y` はどう計算されるのでしょうか。そして、ズームレベルを一つ上げると、タイル番号はどう変わるのでしょうか。

この章は、第I部の Web Mercator と、ここから先の整数の世界をつなぐ章です。

```
Web Mercator の正方形
  ↓
ピクセル座標
  ↓
タイル番号 (x, y)
  ↓
ズームを上げると番号は 2 倍と 2 倍 + 1 に分かれる
```

# 世界が正方形になる理由
%%%
tag := "t-square"
%%%

Web Mercator は $`x = a\lambda`、$`y = a \operatorname{arsinh}(\tan \varphi)` で地球を平面に写します。$`a` は WGS 84 の赤道半径です。経度が $`-\pi`〜$`\pi` を動くと、$`x` は $`-\pi a`〜$`\pi a`（約 ±2003 万 m）を動きます。

{leanDecl Geodesy.Projection.x_mem}

一方、$`y` は極に近づくと際限なく大きくなり、極そのものは地図に描けません。そこで Web 地図は、$`y` がちょうど $`\pi a` になる緯度で地図を切り落とします。すると世界は、一辺 $`2\pi a` の正方形になります。この切り落としの緯度が、よく知られた約 85.0511° です。

{leanDecl Geodesy.Projection.maxLatitude}

{leanDecl Geodesy.Projection.y_mem_iff}

世界が正方形になったことで、正方形のタイルで隙間なく敷き詰められるようになりました。85° より北の地域が Web 地図に表示されないのは、タイルで切るために払った代償です。

# ピクセルとタイル
%%%
tag := "t-pixel-tile"
%%%

ズームレベル $`z` では、正方形の世界が一辺 $`256 \cdot 2^z` ピクセルの画像として描かれます。ズームを一つ上げると、ピクセル座標はちょうど 2 倍になります。

{leanDecl Geodesy.Projection.pixelX_succ}

タイルは 256 × 256 ピクセルの正方形です。ある地点のタイル番号は、そのピクセル座標を 256 で割って切り捨てたものです。

$$`\mathtt{tileX} = \left\lfloor \frac{\mathtt{pixelX}}{256} \right\rfloor = \left\lfloor \frac{x + \pi a}{2\pi a} \cdot 2^z \right\rfloor`

{leanDecl Geodesy.Projection.tileX}

こうして求めたタイルは、たしかにその地点のピクセルを含んでいます。

{leanDecl Geodesy.Projection.tileX_spec}

# 端の扱い：半開区間の正方形
%%%
tag := "t-edges"
%%%

タイル番号は $`0`〜$`2^z - 1` の範囲に入るはずです。けれども、正方形の右端（経度 180°、日付変更線）でこの式を計算すると、番号はちょうど $`2^z` になり、格子の一つ外にはみ出します。下端（南の切り落とし線）でも同じことが起こります。

{leanDecl Geodesy.Projection.tileX_halfExtent}

LeanGeodesy は、右端と下端を含まない半開区間の正方形 $`-\pi a \le x < \pi a`、$`-\pi a < y \le \pi a` の上で、タイル番号が必ず $`0`〜$`2^z - 1` に収まることを証明しています。

{leanDecl Geodesy.Projection.tileX_lt}

実装では、経度 180° の点をどのタイルに入れるかを決めておかないと、番号が一つはみ出すバグになります。タイルのライブラリが端の点を隣のタイルに寄せたり、経度を折り返したりするのは、この境界の問題への対処です。

# ズームを上げると何が起きるか
%%%
tag := "t-zoom"
%%%

ズームを一つ上げるとピクセル座標が 2 倍になるので、ズーム $`z + 1` のタイル番号を 2 で割って切り捨てると、ズーム $`z` のタイル番号に戻ります。言い換えると、ズーム $`z` のタイル $`x` は、ズーム $`z + 1` のタイル $`2x` と $`2x + 1` に分かれます。

{leanDecl Geodesy.Projection.tileX_succ_div_two}

{leanDecl Geodesy.Projection.tileX_succ_eq}

ある地点を含むズーム $`z + 1` のタイルの「親」は、同じ地点を含むズーム $`z` のタイルです。どのズームでも、同じ地点は親子関係でつながったタイルの列に含まれています。

{leanDecl Geodesy.Tiles.parent_tileOfPoint}

一つのタイルが、次のズームで縦横 2 × 2 の 4 枚に分かれる。この構造だけを取り出すと、地図のことはもう忘れてかまいません。次の章では、これを整数だけの世界で考えます。
