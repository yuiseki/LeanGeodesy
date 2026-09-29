import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第7章 回転する惑星の保存則" =>
%%%
file := "clairaut"
tag := "by-clairaut"
%%%

# 消えない数
%%%
file := "conserved"
tag := "by-conserved"
%%%

:::yaruo
$`G\lambda'' + G'\varphi'\lambda'`……あっ、積の微分だお。$`G\lambda'` を時間で微分した形だお。
:::

$$`\frac{d}{dt}\left(G\lambda'\right) = G'\varphi'\lambda' + G\lambda''`

:::yaranaio
二本目の測地線方程式は、こう言っている。
:::

$$`\frac{d}{dt}\left((N\cos\varphi)^2\lambda'\right) = 0`

:::yaruo
$`(N\cos\varphi)^2\lambda'` が、時間で変わらない……。
:::

:::yaranaio
測地線に沿って進むかぎり、方位が変わろうと、緯度が変わろうと、この数は決して変わらない。*保存量*だ。
:::

:::yaruo
どこから、そんな数が湧いてきたんだお。
:::

:::yaranaio
第一基本形式をもう一度見ろ。
:::

$$`ds^2 = M^2\,d\varphi^2 + (N\cos\varphi)^2\,d\lambda^2`

:::yaruo
$`M` も $`N\cos\varphi` も、緯度 $`\varphi` だけで決まってるお。経度 $`\lambda` は……どこにもないお。
:::

:::yaranaio
惑星を地軸のまわりにどれだけ回しても、形は変わらない。*回転対称性*。だからものさしに経度が現れない。そして、形を変えない対称性が一つあるごとに、変わらない量が一つ生まれる。物理で、回転対称な系の角運動量が保存されるのと、まったく同じ構造だ。
:::

:::yaruo
惑星が回転対称だから、その上の最短の道は、保存量を抱えたまま進む……。
:::

# 地軸からの距離と方位
%%%
file := "relation"
tag := "by-relation"
%%%

:::yaranaio
この保存量を、もっと見慣れた形にする。測地線は速さが一定だった。方位角 $`A` の正弦は、東向きの速度 $`N\cos\varphi\cdot\lambda'` を速さで割ったものだ。組み合わせると、地軸からの距離を $`p = N\cos\varphi` として
:::

$$`p\sin A = \text{一定}`

:::yaruo
地軸からの距離と、方位角の正弦の積が、ずっと一定……。
:::

:::yaranaio
*Clairaut の関係*。アレクシ・クレローは、地球がつぶれていることを確かめた十八世紀のラップランド遠征に加わった数学者だ。
:::

:::kimatta
つまり、*Clairaut の関係は、回転する惑星の対称性の影*ということなんだよ。

美しい……
:::

:::theorem "clairaut" (lean := "Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut_G_mul_lon', Geodesy.ReferenceEllipsoid.EllipsoidCurve.sinAzimuth_eq, Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut")
楕円体の測地線に沿って $`(N\cos\varphi)^2\lambda'` は一定であり、地軸からの距離 $`p = N\cos\varphi` と方位角 $`A` について*Clairaut の関係* $`p\sin A = \text{一定}` が成り立つ。これは {uses "geodesic_equations"}[] の経度方程式が、第一基本形式に経度が現れないことから保存則の形をとることの帰結である。
:::

:::proof "clairaut"
経度方程式は $`d(G\lambda')/dt = 0` と同じである。測地線の速さが一定であることと $`\sin A = p\lambda'/\lVert r'\rVert` を組み合わせる。
:::

# 越えられない緯度
%%%
file := "turning-point"
tag := "by-turning-point"
%%%

:::yaruo
$`\sin A` は 1 を超えないお。だから $`p` は、ある値より小さくなれない……。
:::

:::yaranaio
極へ近づけば $`p` は小さくなる。だから測地線は、ある緯度より上には行けない。その最高緯度で $`\sin A = 1`、測地線は真東か真西を向き、引き返す。
:::

:::yaruo
北東へ飛び立った飛行機は、ある緯度で真東を向いて、そこから南東へ降りていく。全部、この一本の式が決めてたのかお。
:::

:::yaranaio
測地線を計算するソフトウェアは、この一定値を出発点の緯度と方位から求め、道のりの計算に使う。
:::

:::yaruo
じゃあ、北緯 45° の緯線を真東に進むのはどうだお。方位は 90° のまま、$`p` も一定だから、$`p\sin A` も一定。保存則を満たしてるお。測地線だお。
:::

:::yaranaio
満たしているのに、測地線ではない。測地線になる緯線は、*赤道だけ*だ。
:::

:::yaruo
なんでだお。
:::

:::yaranaio
緯線に沿って回るとき、加速度は地軸の方を向いている。地軸は緯線の円の中心を通るが、赤道以外では、地面に対して斜めだ。加速度に地面に沿った成分、子午線方向の成分が残る。地面の上から見ると、緯線は極の側へ曲がり続けている道なんだ。
:::

:::theorem "parallels" (lean := "Geodesy.ReferenceEllipsoid.parallelCurve_isGeodesic_iff, Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesicAt_of_conserved")
一定の速さで進む緯線は、{uses "clairaut"}[] の保存量をすべて保つが、測地線であるのは赤道のときに限る。緯度が変化している場所では、保存則から測地線方程式が復元される。
:::

:::proof "parallels"
緯線の加速度は地軸を向き、子午線方向に成分 $`N\cos\varphi\,M\sin\varphi` を持つ。これが 0 になるのは $`\sin\varphi = 0`、すなわち赤道だけである。
:::

# エピローグ
%%%
file := "epilogue"
tag := "by-epilogue"
%%%

:::yaruo
0.001° の話から始まったお。
:::

:::yaranaio
二つの数 $`a` と $`f` が惑星の形を決めた。形が二つの曲率半径を決め、曲率半径が地表のものさしを決めた。ものさしを平面へ押しつぶすと歪みが生まれ、角度を守れという願いが Mercator の式を生み、面積との両立が赤道でしか許されないことが分かった。
:::

:::yaruo
そして同じものさしから、曲がらない道の方程式が出てきて……
:::

:::yaranaio
惑星が回転対称であるというたった一つの事実が、その上を飛ぶすべての飛行機に、一つの数を手放させない。
:::

:::yaruo
全部、つながってたお。
:::

:::yaranaio
そして一つ残らず、Lean が前提から導いた。次のページが、その依存関係の全体図だ。
:::
