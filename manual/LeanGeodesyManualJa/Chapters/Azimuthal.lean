import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "中心から見た距離と方位を守る" =>
%%%
file := "azimuthal"
tag := "ja-azimuthal"
%%%

ある地点から半径 100 km のバッファを作ると、地図上でどんな形になるのでしょうか。GIS のライブラリの中には、バッファを作るときに、その地点を中心とする正距方位図法へいったん投影し、平面上に円を描いてから元に戻すものがあります。この手順は正しいのでしょうか。

この章では、角度でも面積でもなく「中心からの距離と方位」を守る図法を考えます。そのためには、まず地球上の二点間の距離をきちんと決めておく必要があります。

# 球の上の距離：大円距離
%%%
tag := "great-circle-distance"
%%%

球の上の二点を結ぶ最短の道は、二点と球の中心を含む平面が球を切る円、すなわち大円に沿っています。その長さは、中心から見た二点の角度（中心角）に半径をかけたものです。GIS でよく使われるハバーサイン公式は、この中心角を緯度経度から計算する式です。

{leanDecl Geodesy.Geodesic.haversine}

大円が本当に最短であることは、1.6 章であらためて証明を追います。ここでは、この距離を「守りたいもの」として使います。

# 中心からの距離と方位を守る図法
%%%
tag := "azimuthal-equidistant"
%%%

北極を中心とする正距方位図法は、緯度 $`\varphi`、経度 $`\lambda` の地点を、中心から距離 $`R(\pi/2 - \varphi)` の位置に、方向 $`\lambda` で描きます。

$$`x = R\left(\frac{\pi}{2} - \varphi\right) \cos \lambda, \qquad y = R\left(\frac{\pi}{2} - \varphi\right) \sin \lambda`

$`R(\pi/2 - \varphi)` は、北極からその地点までの大円距離そのものです。そして描く方向は、北極からその地点へ向かう大円が出発する方向と一致します。中心から見た距離と方位が、地図上でそのまま読めるのです。

{leanDecl Geodesy.Projection.azimuthalEquidistant}

{leanDecl Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre}

{leanDecl Geodesy.Projection.azimuthalEquidistant_preserves_azimuth}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Azimuthal equidistant keeps distances」）

1.2 章の局所歪みで測ると、子午線方向の縮尺は $`h = 1` で、緯線方向の縮尺は $`k = (\pi/2 - \varphi)/\cos \varphi` です。極以外では $`k > 1` なので、この図法は等角でも正積でもありません。守っているのは、あくまで中心から見た距離と方位だけです。

{leanDecl Geodesy.Projection.one_lt_azimuthalEquidistant_k}

{leanDecl Geodesy.Projection.azimuthalEquidistant_not_isConformal}

# バッファは正しい形で描かれる
%%%
tag := "buffer"
%%%

冒頭の問いに戻ります。中心からの大円距離がちょうど $`r` の地点の集まり（測地円）は、正距方位図法の上では半径 $`r` のユークリッド円に描かれます。距離 $`r` 以内の地点の集まり（測地円板）は、半径 $`r` の円板に描かれます。平面上に円を描いて戻す方法は、球の上では厳密に正しいバッファを与えます。

{leanDecl Geodesy.Projection.image_geodesicDisk}

ただし、形が正しいからといって面積も正しいわけではありません。角半径 $`\theta` の測地円板は球冠で、その面積は $`2\pi R^2(1 - \cos \theta)` です。地図上の円板の面積は $`\pi (R\theta)^2` です。$`1 - \cos \theta < \theta^2/2` なので、どんな半径のバッファも、地図上では実際より大きな面積に描かれます。

{leanDecl Geodesy.Projection.capArea_eq}

{leanDecl Geodesy.Projection.azimuthalEquidistant_enlarges_buffer}

実装上は、正距方位図法で作ったバッファの境界はそのまま使ってよく、その面積を投影した平面で測ってはいけない、ということになります。

# Mercator の直線は出発の方向を教えてくれない
%%%
tag := "mercator-azimuth"
%%%

Web 地図の上で二点を直線で結ぶと、その直線の向きが「出発すべき方向」に見えます。けれども Mercator はこの意味での方位を守りません。

北緯 45° 東経 0° から北緯 45° 東経 90° へ向かう場合を考えます。二点は同じ緯線上にあるので、Mercator の地図上の直線は真東を向きます。ところが二点を結ぶ最短の大円は、北寄りに出発します。Mercator は各地点で角度を守っていますが、それは地図上の直線が最短経路の方向を向くことを意味しません。

{leanDecl Geodesy.Projection.mercator_not_preserves_azimuth}

ここまでで、角度を守る Mercator、面積を守る Lambert、中心からの距離と方位を守る正距方位図法を見てきました。次の章では、それぞれが何を守り、何を壊すのかを並べて比べます。
