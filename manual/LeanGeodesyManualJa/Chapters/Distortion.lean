import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "地球を平面にすると何が壊れるのか" =>
%%%
file := "distortion"
tag := "ja-distortion"
%%%

Web 地図の隅にある縮尺バーは、画面のどこでも正しいのでしょうか。東京を表示しているときと札幌を表示しているときで、同じ長さのバーが同じ距離を表すのでしょうか。

答えは「いいえ」です。Web 地図では、ズームレベル $`z` の 1 ピクセルが地表で $`2\pi a \cos \varphi / (256 \cdot 2^z)` m に当たり、緯度 $`\varphi` によって変わります。縮尺バーが表示中の緯度に合わせて伸び縮みするのはこのためです。

{leanDecl Geodesy.Projection.groundResolution_eq}

曲がった地表を平面に写すと、どこかが必ず伸び縮みします。この章では、その伸び縮みを数として測る方法を作り、角度を守る図法である Mercator がどこから来るのかを見ます。

```
第一基本形式（地表のものさし）
  ↓
地図投影の偏微分（地図の一歩）
  ↓
局所歪み：縮尺 h, k と面積の縮尺
  ↓
等角 ⇔ 第一基本形式のスカラー倍
  ↓
Mercator
```

# 地表の一歩と地図の一歩を比べる
%%%
tag := "compare-steps"
%%%

前の章で、地表での一歩の長さが分かりました。北へ緯度 $`d\varphi` の一歩は $`M\, d\varphi`、東へ経度 $`d\lambda` の一歩は $`N \cos \varphi\, d\lambda` で、二つは直交しています。

地図投影は、この二つの一歩を地図上の二つのベクトルに写します。緯度方向の像を `dLat`、経度方向の像を `dLon` と呼びます。数学ではこれを投影の偏微分、二つを並べた行列をヤコビ行列と呼びます。歪みとは、地図上のベクトルの長さと地表での一歩の長さの比のことです。

$$`h = \frac{\lVert \mathtt{dLat} \rVert}{M}, \qquad k = \frac{\lVert \mathtt{dLon} \rVert}{N \cos \varphi}, \qquad \text{面積の縮尺} = \frac{\lvert \det(\mathtt{dLat}, \mathtt{dLon}) \rvert}{M \cdot N \cos \varphi}`

$`h` は子午線方向の縮尺、$`k` は緯線方向の縮尺です。LeanGeodesy は、地表の基準の長さと地図上の二つのベクトルを組にして、局所歪み `LocalDistortion` という構造にまとめています。

{leanDecl Geodesy.Projection.LocalDistortion}

楕円体の上で測るときの基準の長さは、第一基本形式の $`\sqrt{E} = M` と $`\sqrt{G} = N \cos \varphi` そのものです。第1章のものさしが、そのまま歪みの物差しになっています。

{leanDecl Geodesy.Projection.LocalDistortion.ofEllipsoid}

`dLat` と `dLon` が直交していれば、地表の小さな円は地図上で半軸 $`h` と $`k` の楕円に描かれます。これがティソーの指示楕円で、図法の教科書で地図上に並んでいる小さな楕円の正体です。

{leanDecl Geodesy.Projection.LocalDistortion.tissot}

# 角度を守るとはどういうことか
%%%
tag := "conformal"
%%%

航海図や Web 地図では、交差点の角度や海岸線の形が崩れないことが大事です。どの方向の一歩も同じ倍率で伸び縮みするなら、二つの方向のなす角は変わりません。こうした図法を等角と呼びます。局所歪みの言葉で言うと、「`dLat` と `dLon` が直交し、かつ $`h = k`」です。

{leanDecl Geodesy.Projection.LocalDistortion.isConformal_iff}

第一基本形式を使うと、同じことがもっと見通しよく言えます。等角な図法では、どんな向きの一歩についても

$$`(\text{地図上の長さ})^2 = h^2 \times (\text{第一基本形式で測った地表の長さ})^2`

が成り立ちます。地図は地表のものさしを、場所ごとに決まる一つの数 $`h^2` 倍するだけです。角度は内積の比なので、ものさし全体を同じ数倍しても変わりません。これが「等角とは第一基本形式をスカラー倍で保つこと」の意味です。

{leanDecl Geodesy.Projection.isConformal_iff_firstForm}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Conformal iff it scales the first fundamental form」）

等角かどうかを確かめる手順は、これで決まりました。偏微分を計算し、直交と $`h = k` を確かめればよいのです。では、等角な図法を実際に作るにはどうすればよいでしょうか。

# Mercator は「等角にしたい」から導ける
%%%
tag := "mercator"
%%%

Mercator の北距の式 $`y = R \ln \tan(\pi/4 + \varphi/2)` は、初めて見ると唐突に見えます。けれどもこの式は、等角にしたいという条件から一直線に出てきます。

ここでは半径 $`R` の球で考えます。球では $`M = N = R` です。経線を等間隔の縦線に、緯度 $`\varphi` の緯線を高さ $`R\, g(\varphi)` の横線に描く図法を円筒図法と呼びます。

$$`x = R\lambda, \qquad y = R\, g(\varphi)`

円筒図法では、どの緯線も赤道と同じ長さに描かれます。地表では長さ $`2\pi R \cos \varphi` の緯線が地図では $`2\pi R` になるので、緯線方向の縮尺は、$`g` の選び方によらず $`k = \sec \varphi` に決まってしまいます。一方、子午線方向の縮尺は $`h = \lvert g'(\varphi) \rvert` で、二つの偏微分はいつも直交しています。

{leanDecl Geodesy.Projection.cylindricalDistortion}

直交はすでに満たされているので、等角にするには $`h = k`、すなわち $`g'(\varphi) = \sec \varphi` であればよいことになります。これを積分すると、赤道を $`y = 0` に置いた場合に

$$`g(\varphi) = \operatorname{arsinh}(\tan \varphi) = \ln \tan\left(\frac{\pi}{4} + \frac{\varphi}{2}\right)`

が得られます。Mercator の式は、緯線方向の縮尺 $`\sec \varphi` に子午線方向の縮尺を合わせるために選ばれた関数なのです。

{leanDecl Geodesy.Projection.hasDerivAt_mercatorY}

{leanDecl Geodesy.Projection.mercator_isConformal}

逆向きの主張も証明されています。北を上にして赤道を $`x` 軸に置いた円筒図法のうち、すべての緯度で等角なものは Mercator しかありません。等角という条件が、図法を一つに決めてしまいます。

{leanDecl Geodesy.Projection.eq_mercatorY_of_isConformal}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Mercator is conformal」「Conformal cylindrical projections are Mercator」）

角度を守る代わりに、縮尺 $`\sec \varphi` は緯度とともに大きくなります。北緯 60° では距離が 2 倍、面積が 4 倍に描かれます。グリーンランドがアフリカほどに大きく見えるのはこのためです。

{leanDecl Geodesy.Projection.scaleFactor_60}

{leanDecl Geodesy.Projection.areaFactor_60}

# Web Mercator は楕円体の上では等角ではない
%%%
tag := "web-mercator"
%%%

Web Mercator（EPSG:3857）は「Mercator だから等角」と説明されることが多いのですが、厳密にはそうではありません。

Web Mercator は、WGS 84 の楕円体の緯度経度を、球の Mercator の式にそのまま入れます。楕円体の上で測ると、子午線方向の基準の長さは $`R` ではなく $`M`、緯線方向は $`N \cos \varphi` です。そのため二つの縮尺の比は第1章の $`N / M` になり、扁平な楕円体ではどの緯度でも 1 より大きくなります。地表の小さな円は、地図上でわずかに南北に伸びた楕円に描かれます。

{leanDecl Geodesy.Projection.ellipsoidalMercator_not_isConformal}

WGS 84 では、この比は赤道で最大になり、約 1.00674 です。

{leanDecl Geodesy.Projection.wgs84_equator_scale_ratio}

0.67 % の伸びは、画面上で形を見る分にはまず気になりません。けれども、Web Mercator の平面座標で角度や方位を精密に計算すると、この差がそのまま誤差になります。「Mercator は等角」という性質が成り立つのは球の上での話で、楕円体の座標を球の式に入れた時点で、厳密な等角性は失われています。

等角条件から Mercator は導けました。しかし角度を守る代わりに、面積には何が起きるのでしょうか。
