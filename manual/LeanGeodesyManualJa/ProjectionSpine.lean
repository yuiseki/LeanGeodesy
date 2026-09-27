import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "第一基本形式から Mercator の等角性まで" =>
%%%
file := "projection-spine"
%%%

Web 地図で使われる Mercator 図法は「角度を保つ」と言われます。この章の目的は、その主張を参照楕円体から出発して一歩ずつ理解することです。道筋は次のとおりです。

```
参照楕円体
  ↓
曲率（子午線曲率半径 M、卯酉線曲率半径 N）
  ↓
第一基本形式
  ↓
局所歪み
  ↓
Mercator の等角性
```

各段で使う事実は、すべて LeanGeodesy で証明済みの定理です。定理は Lean の名前と型（signature）だけを示します。これらは実際にビルドしたライブラリから取り込んだもので、手で書き写してはいません。説明はこの本の本文が受け持ちます。

# 出発点：参照楕円体と二つの曲率半径
%%%
file := "ellipsoid-and-curvature"
%%%

地球は、赤道半径 $`a` と扁平率 $`f` で決まる回転楕円体、参照楕円体として扱います。第一離心率の二乗 $`e^2 = f(2 - f)` もここから決まります。

緯度 $`\varphi` の地点で、楕円体の曲がり方は向きによって違います。

- 子午線（南北）方向の曲率半径が子午線曲率半径 $`M = a(1 - e^2) / (1 - e^2 \sin^2 \varphi)^{3/2}` です。
- それと直交する方向の曲率半径が卯酉線曲率半径 $`N = a / \sqrt{1 - e^2 \sin^2 \varphi}` です。その地点を通る緯線は、半径 $`N \cos \varphi` の円になります。

LeanGeodesy は $`M` を公式として置かずに、子午線上の点を $`\varphi` で微分して導いています。

{leanDecl Geodesy.ReferenceEllipsoid.meridianRadius}

{leanDecl Geodesy.ReferenceEllipsoid.primeVerticalRadius}

ここまでで楕円体の「形」は決まりました。けれども、GIS で必要なのは形そのものより、その上での長さ・角度・面積です。それを座標で扱う道具が、次の第一基本形式です。

# 第一基本形式
%%%
file := "first-fundamental-form"
%%%

## 何を測りたいのか
%%%
tag := "what-to-measure"
%%%

地図上で 1 cm が地表で何 m に当たるのかを知るには、まず地表の側で「緯度と経度を少し動かすと、地表をどれだけ進むのか」を知っている必要があります。緯度を $`d\varphi`、経度を $`d\lambda` だけ動かしたとき、地表を進む距離を $`ds` とします。座標の小さな変化と地表の長さを結びつける式が第一基本形式です。

$$`ds^2 = E\, d\varphi^2 + 2F\, d\varphi\, d\lambda + G\, d\lambda^2`

係数 $`E`、$`F`、$`G` は、楕円体上の点 $`r(\varphi, \lambda)` の二つの偏微分ベクトルの内積です。

- $`E = \langle \partial r/\partial\varphi, \partial r/\partial\varphi \rangle`：緯度方向の一歩の長さの二乗
- $`G = \langle \partial r/\partial\lambda, \partial r/\partial\lambda \rangle`：経度方向の一歩の長さの二乗
- $`F = \langle \partial r/\partial\varphi, \partial r/\partial\lambda \rangle`：二つの方向がどれだけ斜めか

つまり第一基本形式は、座標 $`(\varphi, \lambda)` で書かれた小さな一歩について、地表での長さを測るものさしです。長さが測れれば、内積の比として角度も、$`\sqrt{EG - F^2}` として面積も測れます。

## 楕円体ではなぜ E = M²、F = 0、G = (N cos φ)² なのか
%%%
tag := "efg-on-the-ellipsoid"
%%%

$`\partial r/\partial\varphi` は子午線に沿った接ベクトルです。子午線に沿って緯度を少し動かすと、曲率半径 $`M` の弧をたどるので、この接ベクトルの長さは $`M` です。したがって $`E = M^2` です。

$`\partial r/\partial\lambda` は緯線に沿った接ベクトルです。緯線は半径 $`N \cos \varphi` の円なので、経度を少し動かしたときの接ベクトルの長さは $`N \cos \varphi` です。したがって $`G = (N \cos \varphi)^2` です。

子午線と緯線は直角に交わるので、二つの接ベクトルの内積は $`0` で、$`F = 0` です。

{leanDecl Geodesy.ReferenceEllipsoid.firstFormE_eq}

{leanDecl Geodesy.ReferenceEllipsoid.firstFormF_eq}

{leanDecl Geodesy.ReferenceEllipsoid.firstFormG_eq}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)

この三つをまとめると、楕円体上の線素になります。

$$`ds^2 = M^2\, d\varphi^2 + (N \cos \varphi)^2\, d\lambda^2`

{leanDecl Geodesy.ReferenceEllipsoid.norm_dr_sq}

## なぜ地図投影の歪みにつながるのか
%%%
tag := "why-distortion"
%%%

地図投影も、座標 $`(\varphi, \lambda)` の小さな変化を、地図平面上の小さな一歩に写します。歪みとは、地図上の一歩の長さが地表での一歩の長さとどれだけ違うか、ということです。その比較の「地表側」の値を与えるのが第一基本形式です。緯度方向の地表の一歩は $`\sqrt{E} = M`、経度方向は $`\sqrt{G} = N \cos \varphi` で、この二つが歪みを測る基準の長さになります。

次の節では、この基準の長さと地図上の長さを並べて、歪みを数として定義します。

# 局所歪み
%%%
file := "local-distortion"
%%%

## 地表の一歩と地図の一歩を比べる
%%%
tag := "compare-steps"
%%%

ある地点で、北へ緯度 $`d\varphi` だけ進む一歩は地表で長さ $`M\, d\varphi`、東へ経度 $`d\lambda` だけ進む一歩は長さ $`N \cos \varphi\, d\lambda` です。二つは直交しています。

地図投影はこの二つの一歩を、地図上の二つのベクトルに写します。投影の偏微分で、ここでは `dLat`（北向きの一歩の像）と `dLon`（東向きの一歩の像）と呼びます。局所歪みは、この二つのベクトルと地表の基準の長さから決まります。

- 子午線方向の縮尺 $`h = \lVert \mathtt{dLat} \rVert / M`
- 緯線方向の縮尺 $`k = \lVert \mathtt{dLon} \rVert / (N \cos \varphi)`
- 面積の縮尺 $`\lvert \det(\mathtt{dLat}, \mathtt{dLon}) \rvert / (M \cdot N \cos \varphi)`

LeanGeodesy では、この組を `LocalDistortion` という構造にしています。フィールドは、地表の基準の長さ `meridianLength`・ `parallelLength` と、地図上のベクトル `dLat`・ `dLon` です。

{leanDecl Geodesy.Projection.LocalDistortion}

楕円体の上で測るときは、基準の長さを第一基本形式の $`\sqrt{E}` と $`\sqrt{G}` に取ります。

{leanDecl Geodesy.Projection.LocalDistortion.ofEllipsoid}

`dLat` と `dLon` が直交していれば、地表の小さな円は地図上で半軸 $`h`、$`k` の楕円になります。これがティソーの指示楕円です。

{leanDecl Geodesy.Projection.LocalDistortion.tissot}

## 等角とは第一基本形式をスカラー倍で保つこと
%%%
tag := "conformal-first-form"
%%%

等角とは、どの方向の一歩も同じ倍率で伸び縮みすることです。すると、二つの方向のなす角は変わりません。局所歪みの言葉では、「`dLat` と `dLon` が直交し、かつ $`h = k`」と同値です。

{leanDecl Geodesy.Projection.LocalDistortion.isConformal_iff}

これを第一基本形式で言い直すと、見通しがよくなります。等角な投影では、任意の一歩について

$$`(\text{地図上の長さ})^2 = h^2 \times (\text{第一基本形式で測った地表の長さ})^2`

が成り立ちます。地図は地表のものさしを、場所ごとの一つの数 $`h^2` 倍するだけです。角度は内積の比なので、全体を同じ数倍しても変わりません。これが「等角 ⇔ 第一基本形式のスカラー倍保存」の意味です。

{leanDecl Geodesy.Projection.isConformal_iff_firstForm}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)

面積の縮尺も同じ見方で書けます。地図のヤコビアンの面積を、第一基本形式の面積要素 $`\sqrt{EG - F^2}` で割ったものです。

{leanDecl Geodesy.Projection.areaScale_ofEllipsoid}

これで、ある投影が等角かどうかを確かめる手順が決まりました。$`h` と $`k` を計算し、`dLat` と `dLon` の直交を確かめればよいのです。最後に、これを Mercator に当てはめます。

# Mercator の等角性
%%%
file := "mercator"
%%%

## 円筒図法では経度方向の縮尺が先に決まる
%%%
tag := "cylindrical"
%%%

ここからは半径 $`R` の球で考えます。球では $`M = N = R` です。円筒図法は、経線を等間隔の縦線に、緯度 $`\varphi` の緯線を高さ $`R\, g(\varphi)` の横線に描きます。

$$`x = R\lambda, \quad y = R\, g(\varphi)`

経度方向の一歩は、地図上では長さ $`R\, d\lambda`、地表では $`R \cos \varphi\, d\lambda` です。どの緯線も赤道と同じ長さに描かれるので、緯線方向の縮尺は、関数 $`g` の選び方によらず $`k = \sec \varphi` に決まります。

緯度方向の一歩は、地図上では $`R\, g'(\varphi)\, d\varphi`、地表では $`R\, d\varphi` なので、$`h = \lvert g'(\varphi) \rvert` です。また、二つの偏微分 $`(0, R g'(\varphi))` と $`(R, 0)` はいつも直交しています。

{leanDecl Geodesy.Projection.cylindricalDistortion}

## なぜ緯度方向と経度方向の縮尺が一致するのか
%%%
tag := "why-scales-agree"
%%%

直交はすでに満たされているので、等角にするには $`h = k`、つまり $`g'(\varphi) = \sec \varphi` であればよいことになります。Mercator の北距

$$`g(\varphi) = \operatorname{arsinh}(\tan \varphi) = \ln \tan\left(\frac{\pi}{4} + \frac{\varphi}{2}\right)`

は、まさにこの条件を満たすように選ばれた関数で、その導関数は $`\sec \varphi` です。そのため緯度方向の縮尺も $`\sec \varphi` になり、経度方向の縮尺と一致します。

{leanDecl Geodesy.Projection.mercatorY_eq_log_tan}

{leanDecl Geodesy.Projection.hasDerivAt_mercatorY}

{leanDecl Geodesy.Projection.mercator_isConformal}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)

逆も成り立ちます。北を上にして赤道を $`x` 軸に置いた円筒図法のうち、すべての緯度で等角なものはMercator だけです。$`g' = \sec \varphi` という条件が、$`g` を一つに決めてしまうからです。

{leanDecl Geodesy.Projection.eq_mercatorY_of_isConformal}

## 等角の代償
%%%
tag := "cost-of-conformality"
%%%

形は局所的に保たれますが、縮尺 $`\sec \varphi` は緯度とともに大きくなります。北緯 60° では距離が2 倍、面積が 4 倍に描かれます。グリーンランドがアフリカほどに大きく見えるのはこのためです。

{leanDecl Geodesy.Projection.scaleFactor_60}

## Web Mercator は楕円体の上では等角ではない
%%%
tag := "web-mercator-ellipsoid"
%%%

Web Mercator は、楕円体の緯度を球の Mercator の式にそのまま入れます。楕円体の上で測ると、子午線方向の基準の長さは $`R` ではなく $`M`、緯線方向は $`N \cos \varphi` なので、二つの縮尺の比は $`N / M` になります。扁平な楕円体では $`M < N` なので、厳密には等角ではありません。WGS 84 の赤道で約 0.67 % の差です。

{leanDecl Geodesy.Projection.ellipsoidalMercator_not_isConformal}

ここまでで、第一基本形式から Mercator の等角性までを一本の筋として追いました。等積図法や方位図法、測地線など、この先の話は英語版の本で続きます。
