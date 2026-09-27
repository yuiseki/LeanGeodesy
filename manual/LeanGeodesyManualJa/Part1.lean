import VersoManual
import LeanGeodesyManualJa.Chapters.Length
import LeanGeodesyManualJa.Chapters.Distortion
import LeanGeodesyManualJa.Chapters.EqualArea
import LeanGeodesyManualJa.Chapters.Azimuthal
import LeanGeodesyManualJa.Chapters.Tradeoffs
import LeanGeodesyManualJa.Chapters.ShortestPaths
import LeanGeodesyManualJa.Chapters.Clairaut

open Verso.Genre Manual

#doc (Manual) "第I部 地球を測り、平面に写す" =>
%%%
file := "part1"
tag := "ja-part1"
%%%

第I部は、三つの問いを順にたどります。

地球上で「長さ」はどう決まるのか。緯度経度は角度にすぎないので、座標の差を地表の距離に換えるものさしが要ります。第1章で、それを参照楕円体の形から組み立てます。これが第一基本形式です。

地球を平面にすると何が壊れるのか。地図投影は、地表のものさしと地図の上の長さを食い違わせます。第2章から第5章で、その食い違いを数として測り、角度を守る Mercator、面積を守る Lambert、中心からの距離を守る正距方位図法が、それぞれ何を守り何を壊すのかを見ます。

なぜ最短経路はあの形になるのか。第6章と第7章では、地図を離れて地表そのものの上で最短の道を考えます。曲線の長さも、測地線も、Clairaut の保存則も、同じ第一基本形式から出てきます。

```
参照楕円体
  ↓
第一基本形式（地表のものさし）
  ├→ 局所歪み → Mercator / Lambert / 正距方位
  └→ 曲線の長さ → 測地線 → Clairaut の関係
```

{include 1 LeanGeodesyManualJa.Chapters.Length}
{include 1 LeanGeodesyManualJa.Chapters.Distortion}
{include 1 LeanGeodesyManualJa.Chapters.EqualArea}
{include 1 LeanGeodesyManualJa.Chapters.Azimuthal}
{include 1 LeanGeodesyManualJa.Chapters.Tradeoffs}
{include 1 LeanGeodesyManualJa.Chapters.ShortestPaths}
{include 1 LeanGeodesyManualJa.Chapters.Clairaut}
