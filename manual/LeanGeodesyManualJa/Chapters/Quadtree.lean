import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "タイルは四分木になる" =>
%%%
file := "quadtree"
tag := "ja-quadtree"
%%%

Bing Maps の quadkey は、タイルを `"0231"` のような数字の列で表します。桁数はズームレベルに等しく、各桁は 0〜3 のどれかです。この数字は何を表しているのでしょうか。そして、$`(z, x, y)` という表し方と quadkey は、本当に同じものを表しているのでしょうか。

前の章で、一つのタイルが次のズームで 4 枚に分かれることを見ました。この章では、その構造を整数だけで書き、タイルが四分木（quadtree）の節点そのものであることを示します。

# 親と四つの子
%%%
tag := "t-parent-children"
%%%

ズーム $`z` のタイルは、$`x, y < 2^z` を満たす整数の組 $`(x, y)` です。

{leanDecl Geodesy.Tiles.Tile}

ズーム $`z + 1` のタイル $`(x, y)` の親は $`(\lfloor x/2 \rfloor, \lfloor y/2 \rfloor)` です。親から見ると、子は四つあります。四つの子は、$`x` と $`y` の偶奇で区別できます。その区別を一つの数字にしたのが

$$`\text{子の番号} = 2 \cdot (y \bmod 2) + (x \bmod 2)`

で、これが quadkey の一桁です。左上が 0、右上が 1、左下が 2、右下が 3 になります。

{leanDecl Geodesy.Tiles.childDigit}

タイルを「親」と「子の番号」の組に分けても、情報は失われません。ズーム $`z + 1` のタイルと、ズーム $`z` のタイルと 0〜3 の数字の組は、一対一に対応しています。

{leanDecl Geodesy.Tiles.split}

{leanDecl Geodesy.Tiles.card_children}

# タイルは根からの道順
%%%
tag := "t-path"
%%%

この分解を繰り返すと、ズーム $`z` のタイルは、ズーム 0 の一枚のタイル（根）から出発して、「どの子へ進むか」を $`z` 回選んだ道順で表せます。道順は、粗いズームから順に並んだ $`z` 桁の 0〜3 の数字の列で、これがまさに quadkey です。

{leanDecl Geodesy.Tiles.QuadPath}

{leanDecl Geodesy.Tiles.tileEquivPath}

タイルの道順は、親の道順の後ろに自分の子の番号を一桁付け足したものです。quadkey の先頭の何桁かを取り出すと、その祖先のタイルの quadkey になるのはこのためです。

{leanDecl Geodesy.Tiles.tileEquivPath_succ}

冒頭の問いに答えると、$`(z, x, y)` と quadkey は、同じ有限集合を別の書き方で表したものです。変換が一対一であることが証明されているので、どちらで保存しても情報は失われません。

# 祖先と相似な縮小
%%%
tag := "t-ancestor"
%%%

$`k` 世代上の祖先は、親を $`k` 回たどったタイルです。その番号は、$`x` と $`y` をそれぞれ $`2^k` で割って切り捨てたものです。ズームを $`k` 段下げたときのタイル番号の計算と同じです。

{leanDecl Geodesy.Tiles.ancestor}

{leanDecl Geodesy.Tiles.ancestor_val}

# 隣り合うタイル
%%%
tag := "t-adjacent"
%%%

二つのタイルが辺を共有しているとき、隣り合っていると言います。一方の座標が等しく、もう一方の座標がちょうど 1 違うことです。この概念は、あとでタイルの並べ方を比べるときの物差しになります。

{leanDecl Geodesy.Tiles.Adjacent}

タイルは $`(x, y)` の組としても、quadkey の数字の列としても表せました。データベースに入れるには、もう一歩進めて一つの整数にしたくなります。次の章では、四分木の道順をそのまま一つの整数に読み替えます。
