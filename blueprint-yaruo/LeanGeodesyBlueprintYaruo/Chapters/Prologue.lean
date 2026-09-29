import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesyBlueprintYaruo.Dialogue

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "序章 0.001度の亀裂" =>
%%%
file := "prologue"
tag := "by-prologue"
number := false
%%%

:::yaruo
地図アプリで、二点の緯度経度の差を取るお。差に 111 km をかける。はい距離。これで全部だお。
:::

:::yaranaio
北緯 60° で、経度を 1° 動かしてみろ。
:::

:::yaruo
111 km だお。
:::

:::yaranaio
55.8 km だ。半分しかない。
:::

:::yaruo
……は？
:::

:::yaranaio
経線は北極で一点に集まる。高緯度へ行くほど、経度 1° の幅は縮む。
:::

:::yaruo
じゃ、じゃあ緯度は大丈夫だお。緯度 1° は、どこでも 111 km。
:::

:::yaranaio
赤道で 110.57 km。北極の近くで 111.69 km。1 km 以上ずれる。
:::

:::yaruo
緯度は南北に等しい角度で刻んであるお。同じ角度なのに、長さが違うのかお。
:::

:::yaranaio
同じ角度だけ曲がるのに必要な道のりは、道の曲がり方で決まる。*地球は、場所によって曲がり方が違う*。
:::

:::yaruo
地球が、場所によって曲がり方が違う……？
:::

:::yaranaio
その 1 km のずれを追いかけると、どこに行き着くと思う。
:::

:::yaruo
想像もつかないお。
:::

:::yaranaio
惑星の形。曲がった面の上の三平方の定理。世界を平らにする方法と、そのとき必ず壊れるもの。四百年前の地図の式。そして、回転する惑星の上を飛ぶ飛行機が、決して手放さない一つの数だ。
:::

:::yaruo
0.001° の話をしてたはずだお。
:::

:::yaranaio
そうだ。全部、この 0.001° から始まる。ここから先の主張は一つ残らず、Lean で証明されている。
:::
