import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "面積を守ると何を失うのか" =>
%%%
file := "equal-area"
tag := "ja-equal-area"
%%%

Web 地図の上でグリーンランドとアフリカの大きさを比べてよいのでしょうか。EPSG:3857 の座標のままポリゴンの面積を計算したら、正しい面積になるのでしょうか。

前の章で見たとおり、Mercator の面積の縮尺は $`\sec^2 \varphi` です。赤道では 1 ですが、北緯 60° では 4、北緯 80° では 30 を超えます。面積を比べたいなら、面積を守る図法が要ります。この章では、面積を守る条件からどんな図法が出てくるのか、そしてその代わりに何を失うのかを見ます。

# 円筒図法の面積の縮尺
%%%
tag := "cylindrical-area-scale"
%%%

もう一度、球の円筒図法 $`x = R\lambda`、$`y = R\, g(\varphi)` を考えます。前の章で、縮尺は $`h = \lvert g'(\varphi) \rvert`、$`k = \sec \varphi` でした。二つの偏微分は直交しているので、面積の縮尺は二つの縮尺の積 $`h k` です。

$$`\text{面積の縮尺} = \lvert g'(\varphi) \rvert \sec \varphi`

{leanDecl Geodesy.Projection.cylindrical_areaScale}

面積を守るには、この値が 1 であればよいのです。それには $`g'(\varphi) = \cos \varphi` であればよく、赤道を $`y = 0` に置けば $`g(\varphi) = \sin \varphi` になります。これが Lambert の正積円筒図法です。Mercator が「緯線方向の縮尺 $`\sec \varphi` に合わせる」図法だったのに対して、Lambert は「緯線方向の伸び $`\sec \varphi` を、子午線方向の縮み $`\cos \varphi` で打ち消す」図法です。

{leanDecl Geodesy.Projection.lambert_isEqualArea}

ここでも逆が成り立ちます。すべての緯度で面積を守る円筒図法は、Lambert の図法しかありません。

{leanDecl Geodesy.Projection.eq_sin_of_isEqualArea}

# 局所から全体へ：セルの面積
%%%
tag := "cell-area"
%%%

面積の縮尺が 1 というのは、各地点のごく近くでの話です。実務で知りたいのは、行政区画やメッシュのような有限の広がりを持つ領域の面積です。局所的に面積を守れば、全体の面積も守れるのでしょうか。

緯度 $`\varphi_1`〜$`\varphi_2`、経度 $`\lambda_1`〜$`\lambda_2` のセルを考えます。地表での面積は、第1部の面積要素 $`R^2 \cos \varphi` を積分したもので、

$$`\int_{\lambda_1}^{\lambda_2} \int_{\varphi_1}^{\varphi_2} R^2 \cos \varphi \, d\varphi \, d\lambda = R^2 (\lambda_2 - \lambda_1)(\sin \varphi_2 - \sin \varphi_1)`

です。LeanGeodesy は、この積分の被積分関数が第一基本形式の面積要素そのものであることも示しています。

{leanDecl Geodesy.Projection.sphereCellArea_eq}

{leanDecl Geodesy.Projection.sphereCellArea_integrand_eq_areaElement}

円筒図法は、このセルを高さ $`R(g(\varphi_2) - g(\varphi_1))`、幅 $`R(\lambda_2 - \lambda_1)` の長方形に描きます。Lambert の図法では $`g = \sin` なので、二つの面積はすべてのセルでぴったり一致します。

{leanDecl Geodesy.Projection.lambertCylindrical_preserves_cellArea}

Mercator では、赤道より北にあるすべてのセルが、地図上で実際より大きく描かれます。$`\operatorname{arsinh}(\tan \varphi) - \sin \varphi` が単調に増えるからです。

{leanDecl Geodesy.Projection.mercator_enlarges_cellArea}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Lambert keeps cell areas」）

# Web Mercator は赤道でも面積を守らない
%%%
tag := "web-mercator-area"
%%%

球の Mercator では、赤道上の面積の縮尺はちょうど 1 でした。それなら Web Mercator でも、赤道付近の面積はほぼ正しいはずだと考えたくなります。

ところが楕円体の上では、Web Mercator の面積の縮尺は、極を除くすべての緯度で 1 より大きくなります。赤道も例外ではありません。赤道では子午線曲率半径 $`M` が $`a` より小さいので、Web Mercator は南北方向を楕円体の実際の長さより伸ばして描いているのです。

{leanDecl Geodesy.Projection.webMercator_areaScale_gt_one}

{leanDecl Geodesy.Projection.webMercator_not_isEqualArea}

実装上の教訓ははっきりしています。EPSG:3857 の平面座標でポリゴンの面積を計算すると、高緯度で大きく外れるだけでなく、赤道付近でもわずかに過大になります。面積が必要なら、楕円体上で面積要素を積分するか、正積図法に投影してから測る必要があります。

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Web Mercator is not equal-area」）

# 角度と面積は両立しない
%%%
tag := "no-free-lunch"
%%%

Lambert の図法は面積を守りますが、赤道を離れると角度を守りません。子午線方向は $`\cos \varphi` 倍に縮み、緯線方向は $`\sec \varphi` 倍に伸びるので、高緯度ほど形が横につぶれます。

{leanDecl Geodesy.Projection.lambertCylindrical_not_isConformal}

これは Lambert の図法の欠点というより、円筒図法全体の宿命です。等角には $`\lvert g' \rvert = \sec \varphi`、正積には $`\lvert g' \rvert = \cos \varphi` が必要で、$`\sec \varphi = \cos \varphi` となるのは赤道だけです。赤道を離れると、どんな円筒図法も角度と面積の両方を守ることはできません。

{leanDecl Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「No cylindrical projection is conformal and equal-area」）

角度か面積か、円筒図法ではどちらかを選ぶしかありませんでした。では、角度でも面積でもなく、ある一点から見た距離を守ることはできるでしょうか。
