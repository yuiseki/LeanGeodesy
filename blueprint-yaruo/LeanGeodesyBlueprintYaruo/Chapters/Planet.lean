import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第1章 惑星の輪郭" =>
%%%
file := "planet"
tag := "by-planet"
%%%

# 二つの数で惑星を決める
%%%
file := "two-numbers"
tag := "by-two-numbers"
%%%

:::yaruo
地球は球だお。半径 6371 km。
:::

:::yaranaio
自転している。一日に一回、赤道の上の地面は時速 1670 km で回っている。その遠心力で、赤道のあたりが外へ膨らむ。
:::

:::yaruo
どれくらい膨らむんだお。
:::

:::yaranaio
赤道半径 6378.137 km、極半径 6356.752 km。差は 21.4 km。エベレスト二つ分より大きい。
:::

:::yaruo
地球は、つぶれたボールなのかお。
:::

:::yaranaio
楕円を地軸のまわりに回した形、*回転楕円体*だ。形は二つの数で決まる。赤道半径 $`a` と、つぶれ具合の*扁平率* $`f = (a - b)/a`。GPS が使う *WGS 84* では
:::

$$`a = 6378137\ \mathrm{m}, \qquad \frac{1}{f} = 298.257223563`

:::yaruo
小数点以下九桁……。
:::

:::yaranaio
この二つの数で決めた基準の楕円体を、*参照楕円体*と呼ぶ。スマートフォンに表示される緯度経度は、すべてこの楕円体を基準に測られている。
:::

:::definition "reference_ellipsoid" (lean := "Geodesy.ReferenceEllipsoid, Geodesy.wgs84, Geodesy.ReferenceEllipsoid.e2_eq")
*参照楕円体*は、赤道半径 $`a > 0` と扁平率 $`0 \le f < 1` で決まる回転楕円体である。極半径は $`b = a(1 - f)`、第一離心率の二乗は $`e^2 = f(2 - f) = (a^2 - b^2)/a^2`。WGS 84 は $`a = 6378137` m、$`1/f = 298.257223563` を取る。
:::

# 緯度は中心を向いていない
%%%
file := "latitude"
tag := "by-latitude"
%%%

:::yaruo
形が決まれば、緯度は簡単だお。地球の中心から見上げた角度だお。
:::

:::yaranaio
地面に糸で重りを吊るすと、糸はどっちを向く。
:::

:::yaruo
真下。地面に垂直だお。
:::

:::yaranaio
地面に垂直な線、*法線*。人類は何千年も、この糸を基準に星の高さを測り、緯度を決めてきた。だから地図の緯度は、法線が赤道面となす角だ。*測地緯度* $`\varphi` と呼ぶ。
:::

:::yaruo
球なら、法線は中心を通るお。同じことだお。
:::

:::yaranaio
つぶれた楕円体では、法線は中心を外れる。中心から見た角度、*地心緯度* $`\psi` とは別の角になる。
:::

$$`\tan \psi = (1 - e^2) \tan \varphi`

:::yaruo
どれくらい違うんだお。
:::

:::yaranaio
最大で 0.19°。地表の距離にして約 21 km。あなたのスマートフォンの緯度は、地球の中心を向いていない。
:::

:::theorem "geodetic_latitude" (lean := "Geodesy.ReferenceEllipsoid.geocentric_tan, Geodesy.ReferenceEllipsoid.meridianNormal_eq")
楕円体の子午面で*測地緯度* $`\varphi` の点は、法線が赤道面と角 $`\varphi` をなし、その*地心緯度* $`\psi` は $`\tan \psi = (1 - e^2)\tan \varphi` を満たす。二つは球（$`e = 0`）でだけ一致する。この楕円体は {uses "reference_ellipsoid"}[] である。
:::

:::proof "geodetic_latitude"
子午面での点を $`(N\cos\varphi,\ N(1 - e^2)\sin\varphi)` と置くと、楕円の勾配が角 $`\varphi` を向き、中心からの傾きは $`(1 - e^2)\tan\varphi` になる。
:::

# 一つの地点に、二つの半径
%%%
file := "radii"
tag := "by-radii"
%%%

:::yaruo
序章の 1 km のずれ。あれは結局どこから来るんだお。
:::

:::yaranaio
楕円体の上のある地点に立て。北へ歩くとき、足元の地面はある円のように曲がっている。東へ歩くとき、別の円のように曲がっている。
:::

:::yaruo
同じ場所なのに、向きで曲がり方が違うのかお。
:::

:::yaranaio
南北方向の円の半径が*子午線曲率半径* $`M`。東西方向が*卯酉線曲率半径* $`N`。
:::

$$`M = \frac{a(1 - e^2)}{(1 - e^2\sin^2\varphi)^{3/2}}, \qquad N = \frac{a}{\sqrt{1 - e^2\sin^2\varphi}}`

:::yaruo
$`M` は赤道でいくつなんだお。
:::

:::yaranaio
$`b^2/a`、6335 km。北極では $`a^2/b`、6400 km。北へ行くほど地面は平らになり、半径が伸びる。緯度 1° を進むのに必要な道のりも伸びる。
:::

:::yaruo
110.57 km と 111.69 km……！それが 1 km のずれの正体かお。
:::

:::yaranaio
十八世紀、フランスは二つの遠征隊を送った。一つは北極圏のラップランドへ、一つは赤道直下のペルーへ。緯度 1° の長さを測り比べるためだ。北のほうが長かった。地球がつぶれていることは、そうして確かめられた。
:::

:::yaruo
Lean でもそれは言えるのかお。
:::

:::yaranaio
$`M` は赤道から極へ単調に増え、WGS 84 では最初の 1° が最後の 1° より短い。どちらも証明されている。そして二つの半径の比は
:::

$$`\frac{N}{M} = \frac{1 - e^2\sin^2\varphi}{1 - e^2}`

:::yaranaio
つぶれた楕円体では、極を除くすべての地点で $`M < N` だ。この比を覚えておけ。第4章で、世界で最も使われている地図の正体を暴く。
:::

:::theorem "radii" (lean := "Geodesy.ReferenceEllipsoid.meridianRadius, Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst, Geodesy.ReferenceEllipsoid.N_div_M, Geodesy.ReferenceEllipsoid.meridianRadius_strictMonoOn, Geodesy.wgs84_first_degree_lt_last_degree")
緯度 $`\varphi` で、子午線方向の曲率半径は*子午線曲率半径* $`M`、東西方向は*卯酉線曲率半径* $`N` であり、$`N/M = (1 - e^2\sin^2\varphi)/(1 - e^2)`。扁平な楕円体では $`M` は赤道から極へ単調に増え、WGS 84 では緯度の最初の 1° は最後の 1° より短い。曲率は {uses "geodetic_latitude"}[] の子午面の点から導かれる。
:::

:::proof "radii"
子午面の点 $`(N\cos\varphi,\ N(1 - e^2)\sin\varphi)` を $`\varphi` で微分すると $`(-M\sin\varphi,\ M\cos\varphi)` になり、その長さが $`M` である。
:::

:::yaruo
向きごとの半径は分かったお。でも、斜めに歩いたら？
:::

:::yaranaio
それが次の問題だ。どんな向きの一歩でも測れる、たった一本のものさしが要る。
:::
