import VersoManual

/-!
Figures with a caption: `:::figure (src := "figures/x.svg") (alt := "…")` wraps
the caption, and renders as `<figure class="yaruo-figure">` with the image and
a `<figcaption>`. An optional `(width := "420px")` caps the image's width; it
never exceeds the text width. The images live in `LeanGeodesyBookYaruo/figures/`
and are copied next to the pages by the generator; each page has a `<base>`
pointing at the book's root, so `figures/x.svg` resolves from any page.
-/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output (Html)

namespace LeanGeodesyBookYaruo

-- A figure: image source, alt text and maximum width.
block_extension Block.figure (src alt width : String) where
  data := Json.arr #[Json.str src, Json.str alt, Json.str width]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .arr #[.str src, .str alt, .str width] := data
        | reportError "Expected [src, alt, width] JSON for figure" *> pure .empty
      let style := s!"max-width: min(100%, {width});"
      pure {{
        <figure class="yaruo-figure">
          <img src={{src}} alt={{alt}} style={{style}} loading="lazy"/>
          <figcaption>{{← content.mapM blockHtml}}</figcaption>
        </figure>
      }}
  toTeX := none

/-- The image, its alt text and an optional maximum width. -/
structure FigureConfig where
  src : String
  alt : String
  width : Option String

instance : FromArgs FigureConfig DocElabM :=
  ⟨FigureConfig.mk <$> .named `src .string false <*> .named `alt .string false <*>
    .named `width .string true⟩

/-- A figure whose contents are its caption. -/
@[directive]
def figure : DirectiveExpanderOf FigureConfig
  | cfg, stxs => do
    let caption ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other
        (Block.figure $(quote cfg.src) $(quote cfg.alt) $(quote (cfg.width.getD "100%")))
        #[ $[ $caption ],* ])

end LeanGeodesyBookYaruo
