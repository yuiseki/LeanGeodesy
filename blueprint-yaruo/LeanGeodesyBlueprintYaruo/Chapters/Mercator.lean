import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第4章 メルカトルの方程式" =>
%%%
file := "mercator"
tag := "by-mercator"
%%%

# 1569年
%%%
file := "1569"
tag := "by-1569"
%%%

:::yaranaio
1569 年、ゲラルドゥス・メルカトルは一枚の世界地図を出版した。航海士が羅針盤の角度を地図の上にそのまま引ける地図。角度を守る地図だ。
:::

:::yaruo
Web 地図の元祖だお。$`y = \ln\tan(\pi/4 + \varphi/2)`。あの式を思いついた天才だお。
:::

:::yaranaio
メルカトルは、その式を書いていない。
:::

:::yaruo
えっ。
:::

:::yaranaio
彼は緯線の間隔を、作図で少しずつ広げていった。1599 年にエドワード・ライトが数表で間隔を計算し、その数表が $`\ln\tan` の値と一致すると気づかれたのは 1645 年、メルカトルが死んで半世紀後だ。
:::

:::yaruo
式のほうが、後から見つかったのかお。
:::

:::yaranaio
今夜、その式を導く。材料は第3章の一本の条件だけだ。
:::

# 筒をかぶせる
%%%
file := "cylinder"
tag := "by-cylinder"
%%%

:::yaranaio
半径 $`R` の球で考える。球では $`M = N = R`。経線は等間隔の縦線、緯線は横線に描く。緯度 $`\varphi` の緯線を描く高さは、まだ決めない。$`R\,g(\varphi)` と置く。
:::

$$`x = R\lambda, \qquad y = R\,g(\varphi)`

:::yaruo
地球に筒をかぶせて写す、*円筒図法*だお。
:::

:::yaranaio
北緯 60° の緯線は、地表で長さいくつだ。
:::

:::yaruo
半径 $`R\cos 60° = R/2` の円だから、$`\pi R`。赤道の半分だお。
:::

:::yaranaio
地図の上では。
:::

:::yaruo
円筒図法だから、どの緯線も地図の横幅いっぱい、$`2\pi R`……赤道と同じ長さ。2 倍に引き伸ばされてるお。
:::

:::yaranaio
一般には、$`g` をどう選ぼうと、緯線方向の縮尺はこう決まってしまう。
:::

$$`k = \sec\varphi`

:::yaruo
$`g` を選ぶ前から、決まってるのかお。
:::

:::yaranaio
筒をかぶせた瞬間に、東西方向の歪みは確定する。残る自由は南北方向だけだ。緯度を $`d\varphi` 動かすと、地表で $`R\,d\varphi`、地図で $`R\,g'(\varphi)\,d\varphi`。だから $`h = \lvert g'(\varphi)\rvert`。そして `dLat` は縦、`dLon` は横で、いつも直交している。
:::

# 願いを積分する
%%%
file := "integrate"
tag := "by-integrate"
%%%

:::yaruo
直交はもう満たされてるお。等角にするには、あとは $`h = k` だけ。
:::

:::yaranaio
書け。
:::

$$`g'(\varphi) = \sec\varphi`

:::yaruo
これだけかお。
:::

:::yaranaio
これだけだ。北へ伸ばす割合を、緯線が勝手に伸ばされてしまう割合に合わせる。赤道を $`y = 0` に置いて、積分する。
:::

$$`g(\varphi) = \int_0^\varphi \sec t\,dt = \operatorname{arsinh}(\tan\varphi) = \ln\tan\!\left(\frac{\pi}{4} + \frac{\varphi}{2}\right)`

:::yaruo
……出たお。あの式だお。四百年前の地図の式が、たった一行の条件から出てきたお。
:::

:::kimatta
つまり、*Mercator の式は、等角という願いの積分*ということなんだよ。

美しい……
:::

:::yaranaio
しかも、ほかの答えはない。北を上にして赤道を $`x` 軸に置いた円筒図法で、すべての緯度で等角なものは、*Mercator だけ*だ。
:::

:::theorem "mercator" (lean := "Geodesy.Projection.hasDerivAt_mercatorY, Geodesy.Projection.mercatorY_eq_log_tan, Geodesy.Projection.mercator_isConformal, Geodesy.Projection.eq_mercatorY_of_isConformal")
円筒図法 $`x = R\lambda`、$`y = R\,g(\varphi)` の緯線方向の縮尺は $`\sec\varphi` であり、{uses "conformal_first_form"}[] の意味で等角であるための条件 $`g' = \sec\varphi` を満たす唯一の関数は *Mercator の北距* $`g(\varphi) = \operatorname{arsinh}(\tan\varphi) = \ln\tan(\pi/4 + \varphi/2)` である。Mercator 図法は等角である。
:::

:::proof "mercator"
$`\operatorname{arsinh}(\tan\varphi)` の導関数は $`\sec\varphi`。逆に、$`g(0) = 0` で $`g' = \sec\varphi` を満たす関数は、微分が一致する二関数が一点で一致すれば一致するという事実により、これに等しい。
:::

:::yaruo
代償は。
:::

:::yaranaio
縮尺 $`\sec\varphi`。北緯 60° で距離は 2 倍、面積は 4 倍。グリーンランドの面積はアフリカの 14 分の 1 しかないのに、地図の上では同じくらいに見える。極では無限大になる。だから極は描けない。
:::

# Web Mercator の正体
%%%
file := "web-mercator"
tag := "by-web-mercator"
%%%

:::yaruo
完全に理解したお。Web Mercator も Mercator なんだから、等角だお。名前に書いてあるお。
:::

:::yaranaio
今の計算、どこでやった。
:::

:::yaruo
……球の上だお。$`M = N = R` にしたお。
:::

:::yaranaio
Web Mercator、EPSG:3857 は、WGS 84 の*楕円体の*緯度経度を、*球の* Mercator の式にそのまま入れる。地図の側は球の式のまま。地表の側は楕円体だ。
:::

:::yaruo
地表が楕円体だと……北へ一歩は $`M`、東へ一歩は $`N\cos\varphi`……
:::

:::yaranaio
地図の側は、北にも東にも同じ $`a\sec\varphi` 倍で描く。だから
:::

$$`h = \frac{a\sec\varphi}{M}, \qquad k = \frac{a\sec\varphi}{N}, \qquad \frac{h}{k} = \frac{N}{M}`

:::yaruo
$`N/M`……第1章で「覚えておけ」って言われた比だお！ つぶれた楕円体では $`M < N` だから……
:::

:::yaranaio
$`h > k`。地図の上で、すべての地点が南北方向にわずかに引き伸ばされている。*Web Mercator は、楕円体の上では等角ではない*。WGS 84 では、その比は赤道で最大、1.00674。
:::

:::yaruo
世界で一番使われてる地図が、名前どおりの性質を持ってなかったお……。
:::

:::kimatta
つまり、*Web Mercator は等角のはずなのに、つぶれた地球の上では南北に 1.00674 倍伸びる*……

実に興味深い……！！
:::

:::theorem "web_mercator" (lean := "Geodesy.Projection.ellipsoidalMercator_not_isConformal, Geodesy.Projection.wgs84_equator_scale_ratio")
球の Mercator の式を楕円体の緯度経度に適用する *Web Mercator* は、楕円体の上で測ると子午線方向と緯線方向の縮尺の比が $`N/M` になり、扁平な楕円体では等角でない。WGS 84 ではこの比は赤道で約 1.00674 である。これは {uses "mercator"}[] の式に {uses "radii"}[] の比が入り込んだ結果である。
:::

:::proof "web_mercator"
Web Mercator の偏微分は $`a\sec\varphi` 倍の長さを持ち、楕円体の基準の長さ $`M`、$`N\cos\varphi` で割ると $`h/k = N/M > 1` になる。
:::

:::yaranaio
角度を守る代償は、面積だった。じゃあ逆に、面積を守ったらどうなる。
:::
