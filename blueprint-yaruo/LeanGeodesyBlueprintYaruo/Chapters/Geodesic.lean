import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第6章 曲がらない道" =>
%%%
file := "geodesic"
tag := "by-geodesic"
%%%

# 曲がって見える航路
%%%
file := "flight"
tag := "by-flight"
%%%

:::yaruo
東京からサンフランシスコへの航路を Web 地図に描くと、北へ大きく膨らむお。まっすぐ東へ飛べばいいのに。
:::

:::yaranaio
北緯 45° 東経 0° の地点 A から、北緯 45° 東経 90° の地点 B へ行く。二点は同じ緯線の上だ。緯線に沿ってまっすぐ東へ進むと、距離は。
:::

:::yaruo
半径 $`R\cos 45°` の円の四分の一だから、$`\sqrt{2}\pi R/4`。地球の半径の 1.11 倍だお。
:::

:::yaranaio
A と B と地球の中心を通る平面で球を切った円、*大円*に沿って進むと、中心角は $`\pi/3`。距離は $`\pi R/3`、半径の 1.05 倍だ。
:::

:::yaruo
短いお！ しかも北寄りに出発してるお。
:::

:::yaranaio
緯線は、方位を真東に保ち続ける道だ。Mercator の地図の上では直線になる。航海士が愛した道だが、最短ではない。
:::

:::yaruo
地図の上の直線は、地球の上の最短じゃないのかお。
:::

:::yaranaio
地図の上で膨らんで見えるのは、大円を Mercator に描いたからだ。膨らんでいるのは地図のほうで、地球の上ではそれが最短の道だ。
:::

# 大円が最短であることの証明
%%%
file := "shortest"
tag := "by-shortest"
%%%

:::yaruo
大円が最短なんて、当たり前だお。
:::

:::yaranaio
当たり前に聞こえることほど、証明は重い。曲線の上に点を順に取り、隣り合う点どうしの中心角を足す。点をどれだけ細かく取っても、その和の上限を曲線の長さとする。
:::

:::yaruo
細かく刻んで、足し合わせる。
:::

:::yaranaio
そう定義すると、大円の弧の長さはちょうど二点の中心角に等しく、二点を結ぶどんな曲線もそれより短くならない。同じ長さしかない曲線は、大円の弧の上を通るしかない。
:::

:::theorem "great_circle" (lean := "Geodesy.Geodesic.angularLength_greatArc_le, Geodesy.Geodesic.mem_greatArc_of_angularLength_eq, Geodesy.Projection.greatCircleDistance_lt_rhumb_A_B")
球の上の二点を結ぶどんな曲線も、*大円*の弧より短くならない。同じ長さの曲線は大円の弧の上を通る。北緯 45° の二点 A（東経 0°）と B（東経 90°）では、大円距離 $`\pi R/3` は緯線に沿う道の長さ $`\sqrt{2}\pi R/4` より短い。
:::

:::proof "great_circle"
単位ベクトルどうしの角の三角不等式から、曲線を刻んだ中心角の和は二点の中心角以上になる。大円の弧を刻むと、和はちょうど中心角に等しい。
:::

# 曲がらないという条件
%%%
file := "not-turning"
tag := "by-not-turning"
%%%

:::yaruo
楕円体でも、大円を使えばいいお。
:::

:::yaranaio
楕円体の上の最短の道は、平面で切った円にはならない。中心角という道具もない。武器は第2章のものさしだけだ。
:::

:::yaruo
あのものさし、また出てくるのかお。
:::

:::yaranaio
道が曲がるとは何か、から始める。地面の上を進むとき、加速度には二種類ある。地面に垂直な成分は、地面に沿って進む以上、避けられない。地面に沿った成分は、進路を曲げるか、速さを変える。
:::

:::yaruo
地面に沿った加速度がゼロなら、まっすぐ進んでるお。
:::

:::yaranaio
それを*測地線*と呼ぶ。加速度が、北向きの矢印とも東向きの矢印とも直交している道だ。すると、測地線の上では*速さが一定*になる。
:::

:::yaruo
条件は分かったお。でも、それをどうやって計算するんだお。
:::

:::yaranaio
加速度と二本の矢印の内積を、第一基本形式の係数で書き下す。係数は緯度だけで決まるから、微分も緯度についてだけで済む。$`E' = dE/d\varphi`、$`G' = dG/d\varphi` と書くと
:::

$$`E\varphi'' + \tfrac12 E'\varphi'^2 - \tfrac12 G'\lambda'^2 = 0, \qquad G\lambda'' + G'\varphi'\lambda' = 0`

:::yaruo
ものさしの係数と、その微分だけで書けてるお。
:::

:::yaranaio
これが楕円体の*測地線方程式*だ。この二本の方程式を満たす曲線と、曲がらない曲線は、ちょうど同じものになる。
:::

:::theorem "geodesic_equations" (lean := "Geodesy.ReferenceEllipsoid.EllipsoidCurve.IsGeodesic, Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_speed_const, Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesic_iff_equations")
楕円体の上の曲線が*測地線*であること、すなわち加速度が $`\partial r/\partial\varphi` と $`\partial r/\partial\lambda` の両方に直交することは、{uses "first_fundamental_form"}[] の係数で書いた*測地線方程式* $`E\varphi'' + \tfrac12 E'\varphi'^2 - \tfrac12 G'\lambda'^2 = 0`、$`G\lambda'' + G'\varphi'\lambda' = 0` と同値である。測地線の速さは一定である。この節は {uses "great_circle"}[] の楕円体版にあたる。
:::

:::proof "geodesic_equations"
加速度と接ベクトルの内積を、速度と接ベクトルの内積の時間微分から、接ベクトルの変化率との内積を引いたものとして計算し、第一基本形式の係数とその緯度微分で表す。
:::

:::yaruo
二本目の式、なんだか見覚えのある形をしてるお。
:::

:::yaranaio
よく見てみろ。そこに、この物語の最後の秘密がある。
:::
