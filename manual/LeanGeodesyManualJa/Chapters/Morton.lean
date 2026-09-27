import VersoManual
import LeanGeodesy
import LeanGeodesyManualJa.LeanDecl

open Verso.Genre Manual
open LeanGeodesyManualJa

#doc (Manual) "タイルを一列に並べる：Morton 順序" =>
%%%
file := "morton"
tag := "ja-morton"
%%%

タイルやメッシュをデータベースに入れるとき、二つの整数 $`(x, y)` よりも、一つの整数のキーのほうが扱いやすい場面がたくさんあります。インデックスを一本にでき、範囲検索もできるからです。二次元に広がるタイルを一列に並べるには、どうすればよいのでしょうか。

いちばん素直な答えは、前の章の四分木の道順を、そのまま 4 進数の整数として読むことです。これが Morton 符号で、Z 順序曲線とも呼ばれます。

# 親の番号の 4 倍に子の番号を足す
%%%
tag := "t-morton-def"
%%%

Morton 符号は、四分木の構造に沿って再帰的に定義されます。ズーム 0 の唯一のタイルの符号は 0 です。ズーム $`z + 1` のタイルの符号は、親の符号を 4 倍して、自分の子の番号（0〜3）を足したものです。

$$`\text{morton}(t) = 4 \cdot \text{morton}(\text{parent}(t)) + \text{子の番号}(t)`

ズーム $`z` では、符号は $`0`〜$`4^z - 1` のちょうど $`4^z` 個の値を取ります。

{leanDecl Geodesy.Tiles.mortonEquiv}

{leanDecl Geodesy.Tiles.mortonEquiv_succ_val}

# 三つの表し方は同じもの
%%%
tag := "t-three-names"
%%%

これで、ズーム $`z` のタイルに三つの名前ができました。列と行の組 $`(x, y)`、四分木の道順（quadkey）、Morton 符号です。LeanGeodesy は、この三つが互いに一対一に対応していること、そして「$`(x, y)` から道順を経て Morton 符号へ」と「$`(x, y)` から直接 Morton 符号へ」が同じ結果になることを証明しています。

{leanDecl Geodesy.Tiles.tile_path_morton_bijective}

{leanDecl Geodesy.Tiles.mortonEquiv_eq_trans}

実装上の意味は明快です。タイル、quadkey、Morton 符号は、同じ $`4^z` 個の要素からなる有限集合を、三通りに書いたものにすぎません。Morton 符号を 4 進数で $`z` 桁に書くと、それがそのまま quadkey の数字の列になります。

{leanDecl Geodesy.Tiles.mortonEquiv_val_eq_path}

# ビットを交互に並べる
%%%
tag := "t-interleave"
%%%

Morton 符号には、もう一つよく知られた計算方法があります。$`x` と $`y` を 2 進数で書き、そのビットを交互に並べるのです。$`x` の $`i` 桁目は符号の $`2i` 桁目に、$`y` の $`i` 桁目は $`2i + 1` 桁目に入ります。

$$`\text{morton}(x, y) = \sum_i \left( x_i \cdot 4^i + y_i \cdot 2 \cdot 4^i \right)`

「親の 4 倍に子の番号を足す」という四分木の定義と、「ビットを交互に並べる」という実装でよく使われる計算が、同じ値になることが証明されています。

{leanDecl Geodesy.Tiles.morton_eq_interleave}

符号を 4 で割ると親の符号になり、4 で割った余りは子の番号です。ズームを一段下げる操作は、整数の割り算一回で済みます。

{leanDecl Geodesy.Tiles.morton_div_four}

{leanDecl Geodesy.Tiles.morton_tileOfPoint_succ_div_four}

# Z 順序は飛ぶ
%%%
tag := "t-jumps"
%%%

Morton 順序には弱点があります。符号が隣り合う二つのタイルが、地図の上で隣り合っているとは限らないのです。ズーム 1 では、符号 1 のタイルは右上の $`(1, 0)`、符号 2 のタイルは左下の $`(0, 1)` で、辺を共有していません。符号の順にタイルをたどると、Z の字を描くように斜めに飛びます。これが Z 順序曲線という名前の由来です。

{leanDecl Geodesy.Tiles.morton_jumps}

しかも、この飛びは特定のズームだけの偶然ではありません。ズーム 1 以上のすべてのズームで起こります。

{leanDecl Geodesy.Tiles.morton_not_adjacent}

符号の近さが地図上の近さを必ずしも意味しないことは、Morton 符号で範囲検索をするときに、関係のないタイルまで拾ってしまう原因になります。番号が隣なら地図の上でも必ず隣、という並べ方はできないのでしょうか。
