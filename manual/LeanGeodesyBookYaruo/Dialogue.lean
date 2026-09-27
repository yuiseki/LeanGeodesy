import VersoManual

/-!
Speech blocks for the dialogue: `:::yaruo` and `:::yaranaio` wrap one line of
dialogue, rendered with the speaker's name beside it. The styling is in
`LeanGeodesyBookYaruoMain.lean`.
-/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output (Html)

namespace LeanGeodesyBookYaruo

-- One line of dialogue by `who` (`yaruo` or `yaranaio`).
block_extension Block.speech (who : String) where
  data := Json.str who
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .str who := data
        | reportError "Expected string JSON for speech" *> pure .empty
      let name := if who == "yaruo" then "やる夫" else "やらない夫"
      pure {{
        <div class={{s!"speech {who}"}}>
          <div class="speaker">{{name}}</div>
          <div class="words">{{← content.mapM blockHtml}}</div>
        </div>
      }}
  toTeX := none

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

end LeanGeodesyBookYaruo
