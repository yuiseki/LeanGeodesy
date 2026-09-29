import VersoManual

/-!
Speech blocks for the dialogue blueprint: `:::yaruo`, `:::yaranaio` and
`:::kimatta` wrap one line of dialogue, rendered with the speaker's name beside
it. The styling travels with the block through `extraCss`, since the blueprint
generator takes no extra `<head>` content; it also puts Japanese fonts first.
-/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output (Html)

namespace LeanGeodesyBlueprintYaruo

-- One line of dialogue by `who` (`yaruo`, `yaranaio` or `kimatta`).
block_extension Block.speech (who : String) where
  data := Json.str who
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .str who := data
        | reportError "Expected string JSON for speech" *> pure .empty
      let name := match who with
        | "yaruo" => "やる夫"
        | "yaranaio" => "やらない夫"
        | _ => "キマッた学者"
      pure {{
        <div class={{s!"speech {who}"}}>
          <div class="speaker">{{name}}</div>
          <div class="words">{{← content.mapM blockHtml}}</div>
        </div>
      }}
  toTeX := none
  extraCss := [
    r#"
body, p, li, h1, h2, h3, h4, h5, h6, nav, .toc {
  font-family: "Helvetica Neue", "Segoe UI", Roboto, "Hiragino Sans", "Hiragino Kaku Gothic ProN",
    "Yu Gothic", "Noto Sans JP", "Noto Sans CJK JP", Meiryo, Arial, sans-serif;
}
.speech { display: flex; gap: 0.8em; align-items: baseline; margin: 0.55em 0; }
.speech .speaker { flex: 0 0 6.5em; font-weight: 700; font-size: 0.92em; text-align: right; }
.speech .words { flex: 1 1 auto; padding: 0.35em 0.8em; border-radius: 8px; }
.speech .words > p { margin: 0.2em 0; }
.speech.yaruo .speaker { color: #b45309; }
.speech.yaruo .words { background: #fff7ed; border-left: 3px solid #f59e0b; }
.speech.yaranaio .speaker { color: #1d4ed8; }
.speech.yaranaio .words { background: #eff6ff; border-left: 3px solid #3b82f6; }
.speech.kimatta { margin: 1.6em 0; }
.speech.kimatta .speaker { color: #7c3aed; }
.speech.kimatta .words {
  background: linear-gradient(135deg, #1e1b4b, #4c1d95);
  color: #f5f3ff; border-left: 3px solid #a78bfa; padding: 0.8em 1em; font-size: 1.05em;
  letter-spacing: 0.02em;
}
.speech.kimatta .words strong { color: #fde68a; }
code.math.display, .bp_math.display { display: block; max-width: 100%; overflow-x: auto; overflow-y: hidden; }
@media (max-width: 600px) {
  .speech { flex-direction: column; gap: 0.1em; }
  .speech .speaker { flex: none; text-align: left; }
}
"#]

/-- A line of dialogue by やる夫. -/
@[directive]
def yaruo : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.speech "yaruo") #[ $[ $args ],* ])

/-- A line of dialogue by やらない夫. -/
@[directive]
def yaranaio : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.speech "yaranaio") #[ $[ $args ],* ])

/-- The scholar, who appears only when geodesy becomes beautiful. -/
@[directive]
def kimatta : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.speech "kimatta") #[ $[ $args ],* ])

end LeanGeodesyBlueprintYaruo
