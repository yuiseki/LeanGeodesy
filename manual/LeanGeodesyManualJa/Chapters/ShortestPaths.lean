import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "なぜ最短経路はあの形になるのか" =>
%%%
file := "shortest-paths"
tag := "ja-shortest-paths"
%%%

Web 地図に東京からサンフランシスコへの航空路を描くと、北に大きく膨らんだ弧になります。まっすぐ東へ飛んだほうが近そうに見えるのに、なぜ飛行機はわざわざ北へ回るのでしょうか。

この章では、地表の上で最短の道がどんな形をしているのかを考えます。前半は球の上で、地図上の直線と最短経路がなぜ違うのかを見ます。後半は 1.1 章の第一基本形式に戻り、楕円体の上で「曲線の長さ」と「曲がらない曲線」を定義します。

```
第一基本形式
  ↓
曲線の長さ（速さの積分）
  ↓
測地線：曲がらない曲線
  ↓
測地線方程式と保存則（1.7 章）
```

# Mercator の直線は一定の方位の道
%%%
tag := "rhumb"
%%%

Mercator の地図上で引いた直線は、地表ではどんな道なのでしょうか。答えは、コンパスの方位を一定に保ったまま進む道、航程線（ラムライン）です。

方位 $`\alpha` を保って進むと、北向きの成分と東向きの成分の比がいつも同じになります。1.1 章のものさしで書くと、経度の変化率は $`\tan \alpha / \cos \varphi` です。これを積分すると、経度が Mercator の北距 $`\operatorname{arsinh}(\tan \varphi)` の一次式になり、Mercator の地図の上では直線になります。Mercator の地図が航海図として重宝されたのは、この性質のためです。

{leanDecl Geodesy.Projection.constantBearing_iff_mercatorLine}

# 直線は最短ではない
%%%
tag := "rhumb-vs-great-circle"
%%%

北緯 45° 東経 0° の地点 A と、北緯 45° 東経 90° の地点 B を考えます。二点は同じ緯線上にあるので、A から B への航程線は緯線そのもので、真東へ進みます。その長さは $`R \cos 45° \cdot \pi/2 = \sqrt{2}\pi R/4` です。一方、二点を結ぶ大円の中心角は $`\pi/3` で、大円距離は $`\pi R/3` です。$`\pi R/3 < \sqrt{2}\pi R/4` なので、大円のほうが短いのです。

{leanDecl Geodesy.Projection.greatCircleDistance_lt_rhumb_A_B}

この例には、もう一つ意外な事実があります。Web 地図は、地図上の距離に $`\cos \varphi` をかけて地表の距離に換算します。A と B の地図上の距離を北緯 45° の $`\cos 45°` で換算すると、得られるのは緯線の長さ、つまり航程線の長さです。大円距離ではありません。

{leanDecl Geodesy.Projection.mercator_distance_scaled_A_B}

Web 地図の上で二点間を測るツールが「直線距離」を表示するとき、それが何の長さなのかは実装によって違います。地図上の直線を縮尺で換算しただけなら、それは最短距離ではなく、方位一定の道の長さです。

# 大円が最短であることの証明
%%%
tag := "great-circle-shortest"
%%%

大円が最短であることは「よく知られた事実」として扱われがちですが、LeanGeodesy ではきちんと証明されています。

球の上の曲線の長さを、曲線上に点を順に取って、隣り合う点どうしの中心角を足し合わせた値の上限として定義します。そのうえで、大円の弧の長さはちょうど二点の中心角に等しく、同じ二点を結ぶどんな曲線もそれより短くはならないことが示されます。さらに、同じ長さしかない曲線は大円の弧の上を通るしかありません。

{leanDecl Geodesy.Geodesic.angularLength_greatArc_le}

{leanDecl Geodesy.Geodesic.mem_greatArc_of_angularLength_eq}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Great circles are shortest」）

東京からサンフランシスコへの航路が北へ膨らんで見えるのは、大円を Mercator の地図に描いたからです。膨らんでいるのは地図のほうで、地表の上ではそれが最短の道です。

# 楕円体の上の曲線の長さ
%%%
tag := "curve-length"
%%%

球では中心角という便利な道具がありました。楕円体の上ではそれが使えないので、1.1 章の第一基本形式に戻ります。

楕円体の上を動く点 $`(\varphi(t), \lambda(t))` の速さの二乗は $`M^2 \varphi'^2 + (N \cos \varphi)^2 \lambda'^2` でした。曲線の長さは、この速さを時間で積分したものです。地表のものさしで一瞬ごとの長さを測り、それを足し合わせるわけです。

{leanDecl Geodesy.ReferenceEllipsoid.speed_sq_curve}

{leanDecl Geodesy.Projection.curveLength}

# 子午線弧長は曲線の長さそのもの
%%%
tag := "meridian-arc"
%%%

測地学には「子午線弧長」という量があります。赤道から緯度 $`\varphi` まで、子午線に沿って測った距離で、$`m(\varphi) = \int_0^\varphi M(\psi)\, d\psi` と定義されます。楕円体の上では閉じた式がなく、測地計算のソフトウェアは級数展開で求めています。

この定義は、曲率半径 $`M` を積分するという、一見すると特別な式に見えます。けれども、子午線を緯度でパラメータ付けした曲線と見ると、その速さは第一基本形式から $`\sqrt{E} = M` です。したがって子午線弧長は、前の節で定義した曲線の長さそのものです。

{leanDecl Geodesy.Projection.norm_deriv_meridian}

{leanDecl Geodesy.Projection.meridianArc_eq_curveLength}

この定理は、lean-atlas の現在の版では依存グラフに表示されません。lean-atlas が名前に `_eq_` を含む定数をまとめて除外しているためです。

子午線曲率半径 $`M` は赤道で最も小さく（$`b^2/a`）、極で最も大きく（$`a^2/b`）なり、その間で単調に増えます。そのため緯度 1° に当たる子午線の長さは、赤道付近より極付近のほうが長くなります。18 世紀に、ラップランドとペルーで緯度 1° の長さを測り比べて、地球が極方向につぶれていることが確かめられました。LeanGeodesy は、WGS 84 について最初の 1° が最後の 1° より短いことを証明しています。

{leanDecl Geodesy.ReferenceEllipsoid.meridianRadius_strictMonoOn}

{leanDecl Geodesy.wgs84_first_degree_lt_last_degree}

# 曲がらない曲線としての測地線
%%%
tag := "geodesic"
%%%

楕円体の上の最短経路は、大円のような平面曲線にはなりません。そこで最短経路を直接探すかわりに、「曲がらない曲線」を定義します。

地表の上を進むとき、加速度には二種類の成分があります。地表に垂直な成分は、地面に沿って進む以上どうしても生じます。地表に沿った成分は、進路を曲げたり、速さを変えたりします。地表に沿った成分がまったくない曲線、つまり加速度が $`\partial r/\partial\varphi` とも $`\partial r/\partial\lambda` とも直交している曲線を測地線と呼びます。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.IsGeodesic}

この定義からすぐ分かることがあります。地表に沿った加速度がないので、測地線の上では速さが一定です。

{leanDecl Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_speed_const}

測地線を「曲がらない曲線」として定義しました。では、その条件を緯度と経度の式にすると何が出てくるのでしょうか。
