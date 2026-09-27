import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "地球上で「長さ」はどう決まるのか" =>
%%%
file := "length"
tag := "ja-length"
%%%

緯度を 0.001° 動かすと、地表を何 m 進むのでしょうか。経度を 0.001° 動かした場合はどうでしょうか。GIS で座標の差から距離を見積もるとき、多くの人は「1° はおよそ 111 km」という数字を思い浮かべます。けれども、この数字がどこでも使えるわけではありません。

経度 1° の長さは、赤道ではおよそ 111 km ですが、北緯 60° ではその半分ほどになります。経線は極に向かって集まっていくからです。緯度 1° の長さも、実は場所によって少し違います。赤道付近では約 110.6 km、極付近では約 111.7 km です。緯度と経度は角度にすぎず、その差をそのまま距離として扱うことはできません。

座標の差を距離に換えるには、「この場所で、この向きに座標を少し動かすと、地表をどれだけ進むのか」を教えてくれるものさしが要ります。この章では、そのものさしを地球の形から組み立てます。

```
参照楕円体
  ↓
子午線曲率半径 M、卯酉線曲率半径 N
  ↓
第一基本形式
  ↓
長さ・角度・面積
```

# 地球の形を二つの数で決める
%%%
tag := "reference-ellipsoid"
%%%

地球は完全な球ではなく、極の方向に少しつぶれています。測地学ではこれを回転楕円体で近似し、参照楕円体と呼びます。参照楕円体は二つの数で決まります。赤道半径 $`a` と、どれだけつぶれているかを表す扁平率 $`f` です。GPS の基準である WGS 84 では $`a = 6378137` m、$`1/f = 298.257223563` です。

極半径 $`b = a(1 - f)` や、あとで何度も出てくる第一離心率の二乗 $`e^2 = f(2 - f)` は、この二つから計算できます。$`f = 0` なら球です。

{leanDecl Geodesy.ReferenceEllipsoid}

{leanDecl Geodesy.wgs84}

形は決まりました。次の問いは、この形の上で「少し動く」とどれだけ進むのか、です。

# 曲がり方は向きによって違う
%%%
tag := "radii-of-curvature"
%%%

楕円体の上のある地点に立って、北へ少し歩く場合と東へ少し歩く場合を比べます。球なら、どちらも半径 $`R` の円の上を歩くことになります。楕円体では事情が違い、向きによって地面の曲がり方が違います。

南北に歩くとき、足元は子午線という楕円に沿って曲がっています。その曲がり具合を円で近似したときの半径が子午線曲率半径 $`M` です。東西に歩くときの曲がり具合は、卯酉線曲率半径 $`N` で表されます。緯度 $`\varphi` の地点を通る緯線は半径 $`N \cos \varphi` の円なので、東へ経度を少し動かしたときに進む距離は、この半径で決まります。

$$`M = \frac{a(1 - e^2)}{(1 - e^2 \sin^2 \varphi)^{3/2}}, \qquad N = \frac{a}{\sqrt{1 - e^2 \sin^2 \varphi}}`

LeanGeodesy は $`M` を公式として天下りに置いていません。子午線上の点 $`(N \cos \varphi,\ N(1 - e^2) \sin \varphi)` を $`\varphi` で微分し、その速さとして $`M` を導いています。

{leanDecl Geodesy.ReferenceEllipsoid.meridianRadius}

{leanDecl Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst}

二つの半径の比は、あとで地図投影の歪みを測るときに主役になります。

$$`\frac{N}{M} = \frac{1 - e^2 \sin^2 \varphi}{1 - e^2}`

球では $`e = 0` なので比は 1 です。扁平な楕円体では、極を除くすべての地点で $`M < N` になります。赤道のあたりでは、南北方向の曲がり方が東西方向より急なのです。

{leanDecl Geodesy.ReferenceEllipsoid.N_div_M}

曲率半径が分かれば、北へ一歩、東へ一歩の長さは分かります。けれども、斜めに歩いた場合や、長い道のりを歩いた場合はどうでしょうか。どんな向きの一歩でも測れるようにするのが、次の第一基本形式です。

# 地表のものさし：第一基本形式
%%%
tag := "first-fundamental-form"
%%%

楕円体の上の点を、緯度と経度の関数 $`r(\varphi, \lambda)` として空間の中に置きます。緯度を $`d\varphi`、経度を $`d\lambda` だけ動かしたときに地表を進む距離を $`ds` とすると、次の式が成り立ちます。

$$`ds^2 = E\, d\varphi^2 + 2F\, d\varphi\, d\lambda + G\, d\lambda^2`

係数の $`E`、$`F`、$`G` は、二つの偏微分ベクトル $`\partial r/\partial\varphi`（北向きの接ベクトル）と $`\partial r/\partial\lambda`（東向きの接ベクトル）の内積です。$`E` と $`G` はそれぞれの長さの二乗で、$`F` は二つの向きがどれだけ斜めに交わっているかを表します。この二次式が第一基本形式で、座標で書いた小さな一歩を、地表での長さに換えるものさしです。

楕円体では、この係数がすべて前の節の曲率半径で書けます。北向きの接ベクトルの長さは $`M`、東向きの接ベクトルの長さは $`N \cos \varphi` です。さらに子午線と緯線は直角に交わるので、二つの接ベクトルの内積は 0 になります。

$$`E = M^2, \qquad F = 0, \qquad G = (N \cos \varphi)^2`

{leanDecl Geodesy.ReferenceEllipsoid.firstFormE_eq}

{leanDecl Geodesy.ReferenceEllipsoid.firstFormF_eq}

{leanDecl Geodesy.ReferenceEllipsoid.firstFormG_eq}

$`F = 0` は小さな事実に見えますが、この先ずっと効いてきます。緯度方向と経度方向が直交しているので、距離の計算が「南北の成分」と「東西の成分」の二乗和に分かれるのです。

# 長さ・角度・面積が一つの式から出る
%%%
tag := "length-angle-area"
%%%

第一基本形式が優れているのは、長さだけでなく角度と面積も同じ係数から出てくることです。

長さについては、楕円体の上を動く点 $`(\varphi(t), \lambda(t))` の速さの二乗が $`M^2 \varphi'^2 + (N \cos \varphi)^2 \lambda'^2` になります。これを時間で積分すれば、曲線の長さが得られます。この事実は第6章で、最短経路を考えるときの出発点になります。

{leanDecl Geodesy.ReferenceEllipsoid.speed_sq_curve}

角度については、二つの向きのなす角の余弦が、第一基本形式の内積を長さで割ったものになります。平面のベクトルの角度と同じ考え方を、曲がった地表の上でそのまま使えます。

{leanDecl Geodesy.ReferenceEllipsoid.cos_angle_dr}

面積については、座標の小さな長方形 $`d\varphi \times d\lambda` が地表で占める面積が $`\sqrt{EG - F^2}\, d\varphi\, d\lambda = M N \cos \varphi\, d\varphi\, d\lambda` です。楕円体上の面積を求めるとは、この面積要素を積分することです。

{leanDecl Geodesy.ReferenceEllipsoid.areaElement_eq}

冒頭の問いにも答えられます。緯度を $`d\varphi` だけ動かすと $`M\, d\varphi`、経度を $`d\lambda` だけ動かすと $`N \cos \varphi\, d\lambda` だけ進みます。0.001° の長さが場所によって違うのは、$`M` と $`N \cos \varphi` が緯度によって変わるからです。

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「First fundamental form: E = M²」を選ぶと、この章の概念が依存関係として並びます）

これで地表側の長さを測れるようになりました。しかし地図投影の歪みを測るには、今度は地図側の小さな一歩と比較しなければなりません。
