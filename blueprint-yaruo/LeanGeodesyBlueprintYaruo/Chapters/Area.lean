import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "第5章 失われた面積" =>
%%%
file := "area"
tag := "by-area"
%%%

# 面積を守る筒
%%%
file := "lambert"
tag := "by-lambert"
%%%

:::yaruo
同じ筒で、今度は面積を守るお。
:::

:::yaranaio
面積の縮尺は $`h \times k = \lvert g'(\varphi)\rvert \sec\varphi`。これを 1 にしろ。
:::

:::yaruo
$`g' = \cos\varphi`……積分して、$`g = \sin\varphi`。
:::

:::yaranaio
*Lambert の正積円筒図法*だ。緯線方向の伸び $`\sec\varphi` を、子午線方向の縮み $`\cos\varphi` でちょうど打ち消す。
:::

:::yaruo
局所的に面積を守るのは分かったお。でも、県とか国とか、大きな領域の面積は？
:::

:::yaranaio
緯度 $`\varphi_1`〜$`\varphi_2`、経度 $`\lambda_1`〜$`\lambda_2` の区画を考える。地表の面積は、第2章のものさしの面積要素を積分して $`R^2(\lambda_2 - \lambda_1)(\sin\varphi_2 - \sin\varphi_1)`。地図の上の長方形は $`R^2(\lambda_2 - \lambda_1)(g(\varphi_2) - g(\varphi_1))`。
:::

:::yaruo
$`g = \sin` なら、一致するお。どんな区画でも。
:::

:::yaranaio
そして Mercator なら、赤道より北のすべての区画が、実際より大きく描かれる。一つの例外もなく。
:::

:::theorem "equal_area" (lean := "Geodesy.Projection.lambert_isEqualArea, Geodesy.Projection.lambertCylindrical_preserves_cellArea, Geodesy.Projection.mercator_enlarges_cellArea, Geodesy.Projection.webMercator_not_isEqualArea")
*Lambert の正積円筒図法* $`g = \sin` は {uses "local_distortion"}[] の意味で面積の縮尺が 1 であり、あらゆる緯度経度の区画の面積を保つ。Mercator は赤道より北のすべての区画を拡大し、Web Mercator は扁平な楕円体の上でどの緯度でも正積でない。
:::

:::proof "equal_area"
区画の面積は面積要素 $`R^2\cos\varphi` の積分で $`R^2(\lambda_2 - \lambda_1)(\sin\varphi_2 - \sin\varphi_1)`。Mercator では $`\operatorname{arsinh}(\tan\varphi) - \sin\varphi` が単調増加であることから拡大が従う。
:::

# 握手できる場所
%%%
file := "handshake"
tag := "by-handshake"
%%%

:::yaruo
等角なら $`g' = \sec\varphi`。正積なら $`g' = \cos\varphi`。両方を同時に……
:::

:::yaranaio
$`\sec\varphi = \cos\varphi`。これが成り立つ緯度は。
:::

:::yaruo
$`\cos^2\varphi = 1`……$`\varphi = 0`。赤道だけだお。
:::

:::yaranaio
赤道を一歩でも離れれば、どんな円筒図法も、角度と面積の両方を守ることはできない。これは工夫の不足ではない。証明された不可能だ。
:::

:::kimatta
つまり、*角度と面積は、赤道でしか握手できない*ということなんだよ。

美しい……
:::

:::theorem "no_free_lunch" (lean := "Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea, Geodesy.Projection.lambertCylindrical_not_isConformal")
円筒図法がある緯度 $`\varphi` で等角かつ正積ならば $`\varphi = 0` である。とくに Lambert の正積円筒図法は赤道を離れると等角でない。等角の条件は {uses "mercator"}[]、正積の条件は {uses "equal_area"}[] から来る。
:::

:::proof "no_free_lunch"
等角は $`\lvert g'\rvert = \sec\varphi`、正積は $`\lvert g'\rvert\sec\varphi = 1` を要求し、両立は $`\sec^2\varphi = 1` すなわち $`\varphi = 0` のときだけである。
:::

:::yaruo
平らにすると、必ず何かを失う。じゃあ、平らにしなければいいお。
:::

:::yaranaio
その通りだ。地図を捨てて、惑星の表面そのものに戻る。そこで一番短い道を探す。
:::
