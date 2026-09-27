import VersoManual
import LeanGeodesyBookYaruo.Story.Length
import LeanGeodesyBookYaruo.Story.Flatten
import LeanGeodesyBookYaruo.Story.Mercator
import LeanGeodesyBookYaruo.Dialogue

open Verso.Genre Manual
open LeanGeodesyBookYaruo

#doc (Manual) "やる夫が Lean で学ぶ測地学" =>
%%%
shortTitle := "やる夫の測地学"
tag := "yaruo-top"
%%%

GIS を毎日のように使っているやる夫と、測地学と数学と Lean に詳しいやらない夫の二人が、GIS の裏にある数学を一つずつ確かめていく本です。

:::yaruo
EPSG:4326 も Web Mercator もタイルも、毎日使ってるお。数式を見ると身構えるけど、仕組みは知りたいお。
:::

:::yaranaio
いい心がけだ。定義を読み上げるところからは始めない。お前が普段思っている疑問から始めて、必要になったところで数学を持ち出す。
:::

:::yaruo
Lean って何に使うんだお。
:::

:::yaranaio
説明が本当に正しいかを確かめるためだ。俺が話した内容が、前提からちゃんと導けることを、Lean が一つずつ検査している。本文には、その定理の名前と型を、実際にビルドしたライブラリから取り込んで載せる。手で書き写したものじゃない。
:::

この本に出てくる Lean の定理は、すべて LeanGeodesy で証明済みです。要所には、依存関係を Lean Atlas で見るためのリンクもあります。Atlas で主定理を選ぶと、いま読んだ概念が形式的にどんな依存関係になっているのかを確かめられます。

いまは会話形式の第1部〜第3部まであります。

- 第1部 地球の上で長さを測る：緯度経度の差を、そのまま距離にしてはいけないのか？
- 第2部 地球を無理やり平らにする：地図にすれば、距離は簡単になるのか？
- 第3部 Mercator はなぜあの式なのか：あの式は、昔の人が思いついただけなのか？

この先は、第4部「最短経路はなぜ曲がるのか」、第5部「Web 地図を整数で切り刻む」と続ける予定です。それまでの間、面積を守る図法、最短経路と Clairaut の関係、タイル番号の数学は、散文で書いた[日本語版](https://yuiseki.github.io/LeanGeodesy/manual-ja/)で読めます。

用語は次の表記で統一します。Lean の識別子は翻訳しません。

- reference ellipsoid：参照楕円体
- geodetic latitude：測地緯度
- meridian radius of curvature：子午線曲率半径
- prime vertical radius of curvature：卯酉線曲率半径
- first fundamental form：第一基本形式
- map projection：地図投影
- local distortion：局所歪み
- conformal：等角
- geodesic：測地線

{include 1 LeanGeodesyBookYaruo.Story.Length}
{include 1 LeanGeodesyBookYaruo.Story.Flatten}
{include 1 LeanGeodesyBookYaruo.Story.Mercator}
