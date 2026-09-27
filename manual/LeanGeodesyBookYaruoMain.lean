import VersoManual
import LeanGeodesyBookYaruo

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

/-- Speech blocks for the dialogue (`LeanGeodesyBookYaruo.Dialogue`). -/
def dialogueStyle : Verso.Output.Html := {{
  <style>
    ".speech { display: flex; gap: 0.8em; align-items: baseline; margin: 0.55em 0; }
     .speech .speaker { flex: 0 0 5.5em; font-weight: 700; font-size: 0.92em; text-align: right; }
     .speech .words { flex: 1 1 auto; padding: 0.35em 0.8em; border-radius: 8px; }
     .speech .words > p { margin: 0.2em 0; }
     .speech.yaruo .speaker { color: #b45309; }
     .speech.yaruo .words { background: #fff7ed; border-left: 3px solid #f59e0b; }
     .speech.yaranaio .speaker { color: #1d4ed8; }
     .speech.yaranaio .words { background: #eff6ff; border-left: 3px solid #3b82f6; }
     @media (max-width: 600px) {
       .speech { flex-direction: column; gap: 0.1em; }
       .speech .speaker { flex: none; text-align: left; }
     }"
  </style>
}}

def main := manualMain (%doc LeanGeodesyBookYaruo) (config := { extraHead := #[japaneseFonts, dialogueStyle] })
