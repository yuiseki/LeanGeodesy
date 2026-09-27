import VersoManual

/-!
`{leanDecl Name}` shows a declaration's name, kind and signature, taken from the
built library like `{docstring Name}`, but without its docstring, fields or
constructor. The Japanese book explains each declaration in its own prose, so
the English docstring is left out, while the signature is still the library's
own rather than a copy.
-/

open Lean
open Verso.Doc.Elab
open Verso.ArgParse
open Verso.Genre.Manual

namespace LeanGeodesyManualJa

/-- The declaration to show. -/
structure LeanDeclConfig where
  name : Ident × Name

instance : FromArgs LeanDeclConfig DocElabM :=
  ⟨LeanDeclConfig.mk <$> .positional `name .documentableName⟩

/-- Show a declaration's signature without its docstring. -/
@[block_command]
def leanDecl : BlockCommandOf LeanDeclConfig
  | ⟨(_, name)⟩ => do
    let declType ← Block.Docstring.DeclType.ofName name (hideFields := true)
      (hideStructureConstructor := true)
    let signature ← Signature.forName name
    ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature)
          none #[])
        #[])

end LeanGeodesyManualJa
