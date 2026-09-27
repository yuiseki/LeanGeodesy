import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl
import LeanGeodesyManualJa.Dialogue

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "第3部 Mercator はなぜあの式なのか" =>
%%%
file := "mercator"
tag := "ja-story-mercator"
%%%

「Mercator の式って、昔の人が思いついただけ？」という問いから始めます。

# 円筒図法では、経度方向の縮尺が先に決まる
%%%
file := "cylindrical"
tag := "s3-cylindrical"
%%%

:::yaruo
Mercator の式は知ってるお。$`y = \ln \tan(\pi/4 + \varphi/2)`。なんでこんな形なのかは知らないお。昔の天才がひらめいたんだお。
:::

:::yaranaio
メルカトル自身は、この式を書いていないんだ。式は後の時代に求められた。今日は、この式を自分で作ってみよう。
:::

:::yaruo
作れるわけないお。$`\ln` と $`\tan` が入れ子になってるお。
:::

:::yaranaio
まず、地図の形を決める。話を簡単にするために、半径 $`R` の球で考えよう。球では $`M = N = R` だ。経線は等間隔の縦線、緯線は横線にする。緯度 $`\varphi` の緯線をどの高さに描くかだけは、まだ決めないでおく。高さを $`R\,g(\varphi)` と書いておこう。
:::

$$`x = R\lambda, \qquad y = R\,g(\varphi)`

:::yaruo
地球に筒をかぶせて写すやつだお。円筒図法だお。
:::

:::yaranaio
そうだ。この形にした時点で、もう決まってしまうことがある。緯度 60° の緯線は、地表で長さいくらだ。
:::

:::yaruo
緯線の半径が $`R \cos 60° = R/2` だから、長さは $`\pi R` だお。赤道の半分だお。
:::

:::yaranaio
地図の上ではその緯線は何の長さに描かれる。
:::

:::yaruo
円筒図法だから、どの緯線も横幅いっぱいの……あっ、赤道と同じ $`2\pi R` だお。
:::

:::yaranaio
つまり緯線方向には 2 倍に引き伸ばされている。一般に、緯線方向の縮尺は、$`g` をどう選んでも
:::

$$`k = \frac{1}{\cos \varphi} = \sec \varphi`

:::yaranaio
に決まってしまう。$`g` を選ぶ前から、経度方向の歪みは決まっているんだ。
:::

:::yaruo
子午線方向はどうなんだお。
:::

:::yaranaio
緯度を $`d\varphi` だけ動かすと、地表では $`R\,d\varphi` 進み、地図の上では $`R\,g'(\varphi)\,d\varphi` 動く。だから $`h = \lvert g'(\varphi) \rvert` だ。それから、`dLat` は縦向き、`dLon` は横向きだから、二つはいつも直交している。
:::

{leanDecl Geodesy.Projection.cylindricalDistortion}

# 等角にしろ、と言うだけで式が出る
%%%
file := "derive"
tag := "s3-derive"
%%%

:::yaruo
直交はもう満たされてるお。第2部の話だと、等角にするには、あとは $`h = k` だけでいいお。
:::

:::yaranaio
そうだ。書いてみろ。
:::

:::yaruo
$`h = \lvert g'(\varphi) \rvert`、$`k = \sec \varphi` だから……
:::

$$`g'(\varphi) = \sec \varphi`

:::yaruo
これだけかお。
:::

:::yaranaio
これだけだ。北へ伸ばす割合を、緯線が勝手に伸ばされてしまう割合に合わせる。それが等角という条件の中身だ。あとは積分するだけでいい。赤道を $`y = 0` に置くと
:::

$$`g(\varphi) = \int_0^\varphi \sec t\,dt = \operatorname{arsinh}(\tan \varphi) = \ln \tan\left(\frac{\pi}{4} + \frac{\varphi}{2}\right)`

:::yaruo
……出たお。あの式だお。
:::

:::yaranaio
Mercator の式は覚えるものじゃない。「等角な円筒図法を作れ」と言われたら、誰がやってもこの式に行き着く。
:::

:::yaruo
本当かお。途中の積分でごまかしてないかお。
:::

:::yaranaio
Lean ではこう確かめられている。北距の関数の導関数が $`\sec \varphi` であること、それが教科書の $`\ln \tan` の形と一致すること、そしてこの図法が等角であることだ。
:::

{leanDecl Geodesy.Projection.hasDerivAt_mercatorY}

{leanDecl Geodesy.Projection.mercatorY_eq_log_tan}

{leanDecl Geodesy.Projection.mercator_isConformal}

:::yaruo
別の関数でも等角になったりしないのかお。
:::

:::yaranaio
ならない。北を上にして赤道を $`x` 軸に置いた円筒図法で、すべての緯度で等角なものは Mercator しかない。$`g' = \sec \varphi` という条件が、$`g` を一つに決めてしまうからだ。
:::

{leanDecl Geodesy.Projection.eq_mercatorY_of_isConformal}

[依存関係を Lean Atlas で見る](https://yuiseki.github.io/LeanGeodesy/atlas/)（主定理「Mercator is conformal」「Conformal cylindrical projections are Mercator」）

# 等角の代償
%%%
file := "cost"
tag := "s3-cost"
%%%

:::yaruo
等角なら第2部の話で、面積は $`h^2` 倍だお。Mercator だと $`h = \sec \varphi` だから……
:::

:::yaranaio
面積は $`\sec^2 \varphi` 倍だ。北緯 60° なら。
:::

:::yaruo
$`\sec 60° = 2` だから、距離が 2 倍、面積が 4 倍だお。グリーンランドがアフリカくらいに見えるのは、これかお。
:::

{leanDecl Geodesy.Projection.scaleFactor_60}

{leanDecl Geodesy.Projection.areaFactor_60}

:::yaranaio
そうだ。極では $`\sec \varphi` が無限大になるから、極はそもそも地図に描けない。
:::

# Web Mercator も等角なんだろ？
%%%
file := "web-mercator"
tag := "s3-web-mercator"
%%%

:::yaruo
よし、完全に理解したお。Web Mercator も Mercator なんだから等角だお。名前にそう書いてあるお。
:::

:::yaranaio
ここまでの話は、どこで考えていた。
:::

:::yaruo
……球の上だお。$`M = N = R` にしたお。
:::

:::yaranaio
Web Mercator、つまり EPSG:3857 は、WGS 84 の楕円体の緯度経度を、球の Mercator の式にそのまま入れる。地図の側は球の式のままなのに、地表の側は楕円体だ。
:::

:::yaruo
地表が楕円体だと、何が変わるんだお。
:::

:::yaranaio
地表の一歩の長さだ。第1部で見たとおり、楕円体では北へ一歩が $`M\,d\varphi`、東へ一歩が $`N \cos \varphi\,d\lambda` で、$`M` と $`N` は違う。地図の側は球の式だから、北にも東にも同じ $`a \sec \varphi` 倍で描く。すると二つの縮尺は
:::

$$`h = \frac{a \sec \varphi}{M}, \qquad k = \frac{a \sec \varphi}{N}`

:::yaruo
分母が違うお。$`h = k` にならないお。
:::

:::yaranaio
二つの比は $`h/k = N/M` だ。第1部で「覚えておいてくれ」と言った比だな。扁平な楕円体では、極を除くどこでも $`M < N` だった。
:::

:::yaruo
じゃあ $`h > k` だから、地図の上で南北方向に少し伸びてるお。Web Mercator は、楕円体の上で見ると等角じゃないのかお。
:::

{leanDecl Geodesy.Projection.ellipsoidalMercator_not_isConformal}

:::yaranaio
そういうことだ。WGS 84 では、この比は赤道でいちばん大きく、約 1.00674 になる。
:::

{leanDecl Geodesy.Projection.wgs84_equator_scale_ratio}

:::yaruo
0.67 % かお。画面で見ている分には分からないお。
:::

:::yaranaio
見る分にはな。でも EPSG:3857 の平面座標で角度や方位を精密に計算すると、この差がそのまま誤差になる。「Mercator は等角」は球の上の話で、楕円体の座標を球の式に入れた時点で、厳密な等角性はなくなっているんだ。
:::

:::yaruo
名前を信じちゃいけないお……。
:::

:::yaranaio
次は、地図を離れて地球の上に戻る。Google マップで航空路を引くと、地図の上で曲がって見えるだろ。最短の道がなぜ曲がるのか。そこで第1部のものさしが、もう一度主役になる。
:::
