import VersoManual
import LeanGeodesyManualJa

open Verso Doc
open Verso.Genre Manual
open Verso.Output.Html

/-- Verso's default font stack has no Japanese font, and the fallback it lands
on can set `、` as a narrow glyph. Put common Japanese fonts in the stack. -/
def japaneseFonts : Verso.Output.Html := {{
  <style>
    "body, p, li, h1, h2, h3, h4, h5, h6, nav, .toc {
      font-family: \"Helvetica Neue\", \"Segoe UI\", Roboto, \"Hiragino Sans\",
        \"Hiragino Kaku Gothic ProN\", \"Yu Gothic\", \"Noto Sans JP\", \"Noto Sans CJK JP\",
        Meiryo, Arial, sans-serif;
    }"
  </style>
}}

def main := manualMain (%doc LeanGeodesyManualJa) (config := { extraHead := #[japaneseFonts] })
