import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanGeodesyBlueprintYaruo.Dialogue
import LeanGeodesyBlueprintYaruo.Chapters.Prologue
import LeanGeodesyBlueprintYaruo.Chapters.Planet
import LeanGeodesyBlueprintYaruo.Chapters.Ruler
import LeanGeodesyBlueprintYaruo.Chapters.Flatten
import LeanGeodesyBlueprintYaruo.Chapters.Mercator
import LeanGeodesyBlueprintYaruo.Chapters.Area
import LeanGeodesyBlueprintYaruo.Chapters.Geodesic
import LeanGeodesyBlueprintYaruo.Chapters.Clairaut

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LeanGeodesyBlueprintYaruo

#doc (Manual) "やる夫で学ぶ測地学 Blueprint" =>
%%%
shortTitle := "やる夫 Blueprint"
tag := "by-top"
%%%

:::yaruo
緯度経度の差に 111 km をかければ、距離だお。
:::

:::yaranaio
その考えが、どこで壊れるか。壊れた先に何があるか。全部見せてやる。
:::

登場するのは三人です。GIS を毎日使うやる夫。測地学と数学と Lean を知るやらない夫。そして、測地学が最も美しくなる瞬間にだけ現れるキマッた学者。

物語の要所には、定理のノードが置かれています。ノードの主張はすべて LeanGeodesy で証明済みで、宣言はビルドしたライブラリにリンクしています。最後の依存グラフで、物語全体が一本の証明の連鎖として見えます。

{include 0 LeanGeodesyBlueprintYaruo.Chapters.Prologue}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Planet}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Ruler}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Flatten}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Mercator}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Area}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Geodesic}
{include 0 LeanGeodesyBlueprintYaruo.Chapters.Clairaut}

{blueprint_graph}
{blueprint_summary}
