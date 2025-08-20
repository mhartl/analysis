import Lean.Data.Json
import VersoBlog
import SubVerso.Highlighting.Highlighted
import SubVerso.Module
import Std.Data.HashMap

open Std
open SubVerso.Module
open SubVerso.Highlighting
open Lean

section
variable [Monad m] [MonadError m] [MonadQuotation m]



partial def getCommentString' (pref : String) (hl : Highlighted) : m String := do
  let str := (← getString hl).trim
  let str := str.stripPrefix pref |>.stripSuffix "-/" |>.trim
  pure str
where getString : Highlighted → m String
  | .text txt | .unparsed txt => pure txt
  | .tactics .. => throwError "Tactics found in module docstring!"
  | .point .. => pure ""
  | .span _ hl => getCommentString' pref hl
  | .seq hls => do return (← hls.mapM getString).foldl (init := "") (· ++ ·)
  | .token ⟨_, txt⟩ => pure txt

partial def getDocCommentString : Highlighted -> m String := getCommentString' "/--"
end

def loadModuleContent (mod : String) (leanProject : System.FilePath := "../analysis")
    (overrideToolchain : Option String := none) : IO (Array (ModuleItem × Array (String × Highlighted))) := do

  let projectDir := ((← IO.currentDir) / leanProject).normalize

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists <||> lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let lakeConfig := if (← lakefile.pathExists) then lakefile else lakefile'
  let toolchain ← match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let f ← IO.FS.Handle.mk lakeConfig .read
  f.lock (exclusive := true)
  let jsonFile ←
    try

      let cmd := "elan"
      let args := #["run", "--install", toolchain, "lake", "build", s!"+{mod}:literate"]

      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then
        reportFail projectDir cmd args res

      let args := #["run", "--install", toolchain, "lake", "query", s!"+{mod}:literate"]

      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then
        reportFail projectDir cmd args res
      IO.FS.readFile res.stdout.trim
    finally f.unlock

  let .ok (.arr json) := Json.parse jsonFile
    | throw <| IO.userError s!"Expected JSON array"
  match json.mapM deJson with
  | .error err =>
    throw <| IO.userError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
  | .ok val => pure val

where
  deJson (v : Json) : Except String (ModuleItem × Array (String × Highlighted)) := do
    let item ← FromJson.fromJson? (α := ModuleItem) v
    let terms ← v.getObjVal? "terms"
    let terms ← terms.getObj?
    let terms ← terms.toArray.mapM fun ⟨k, v⟩ => (k, ·) <$> FromJson.fromJson? v
    return (item, terms)
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : System.FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr

open Verso.Genre.Blog Literate

def codeOpts : CodeOpts := { contextName := `name }

open Verso Doc Elab PartElabM in
open Verso.Genre Blog in
open Lean.Parser.Command in
partial def docFromModAndTerms
    (config : LitPageConfig) (content : Array (ModuleItem × Array (String × Highlighted)))
    (rewriter : Array (List Pat × List Literate.Template)) : PartElabM Unit := do
  let mut mdHeaders : Array Nat := #[]
  for cmd in content do
    let ({kind, code, ..}, tms) := cmd
    let tms := HashMap.emptyWithCapacity tms.size |>.insertMany tms
    match kind with
    | ``Lean.Parser.Module.header =>
      if config.header then
        addBlock (← ``(Block.other (BlockExt.highlightedCode codeOpts $(quote code)) Array.mkArray0))
      else pure ()
    | ``moduleDoc =>
      let str ← getModuleDocString code
      let some ⟨mdBlocks⟩ := MD4Lean.parse str
        | throwError m!"Failed to parse Markdown: {str}"
      for b in mdBlocks do
        match b with
        | .header lvl txt =>
          let inlines ← txt.mapM (ofInline tms)

          if let some realLevel := mdHeaders.findRev? (· ≤ lvl) then
            closePartsUntil realLevel ⟨0⟩ -- TODO endPos
            mdHeaders := mdHeaders.take realLevel
          else
            mdHeaders := #[]

          -- The new header could be a sibling or a child. If this is true, it's a child:
          if !mdHeaders.back?.isEqSome lvl then
            mdHeaders := mdHeaders.push lvl

          push {
            titleSyntax := (← arr inlines),
            expandedTitle := some (txt.map inlineText |>.toList |> String.join, inlines),
            metadata := none,
            blocks := #[],
            priorParts := #[]
          }
        | other =>
          addBlock (← ofBlock tms other)
          -- Only convert doccomments if the option is turned on
    | ``declaration | `lemma =>
      match code with
      | .seq s =>
        -- Find the index corresponding to the docComment
        let docCommentIdx := s.findIdx? (fun
          | (.token ⟨.docComment, _⟩) => true
          | _ => false)
        match docCommentIdx with
        | some i =>
          let codeBefore ← ``(Block.other
            (BlockExt.highlightedCode codeOpts $(quote (Highlighted.seq s[:i]))) Array.mkArray0)
          let some ⟨mdBlocks⟩ := MD4Lean.parse (← getDocCommentString s[i]!)
            | throwError m!"Failed to parse Markdown: {← getDocCommentString s[i]!}"
          let docCommentBlocks ← mdBlocks.mapM (fun b => ofBlock tms b)
          let codeAfter ←``(Block.other (BlockExt.highlightedCode codeOpts $(quote (Highlighted.seq s[i+1:]))) Array.mkArray0)
          let blocks := #[codeBefore] ++ docCommentBlocks ++ #[codeAfter]
          addBlock (← ``(Block.other (BlockExt.htmlDiv "declaration") #[$blocks,*]))
        | none =>
          -- No docComment attached to declaration, render definition as usual
          addBlock (← ``(Block.other (BlockExt.highlightedCode codeOpts $(quote code)) Array.mkArray0))
      | _ => addBlock (← ``(Block.other (BlockExt.highlightedCode codeOpts $(quote code)) Array.mkArray0))

    | ``eval | ``evalBang | ``reduceCmd | ``print | ``printAxioms | ``printEqns | ``«where» | ``version | ``synth | ``check =>
      addBlock (← ``(Block.other (BlockExt.highlightedCode codeOpts $(quote code)) Array.mkArray0))
      if let some msg := getFirstMessage code then
        let msg : Highlighted.Message := ⟨msg.1, msg.2⟩
        addBlock (← ``(Block.other (Blog.BlockExt.message false $(quote msg) []) #[]))
    | _ =>
      addBlock (← ``(Block.other (BlockExt.highlightedCode codeOpts $(quote code)) Array.mkArray0))
  closePartsUntil 0 ⟨0⟩ -- TODO endPos?
where
  arr (xs : Array Term) : PartElabM Term := do
    if xs.size ≤ 8 then
      pure <| Syntax.mkCApp (`Array ++ s!"mkArray{xs.size}".toName) xs
    else
      `(#[$xs,*])

  ofBlock (tms : HashMap String Highlighted) : MD4Lean.Block → PartElabM Term
  | .header .. => throwError "Headers should be processed at the part level"
  | .p txt => do
    let inlines ← txt.mapM (ofInline tms)
    ``(Block.para $(← arr inlines))
  | .ul _ _ lis => do
    ``(Doc.Block.ul $(← arr (← lis.mapM (ofLi tms))))
  | .ol _ start _ lis => do
    ``(Doc.Block.ol $(quote (start : Int)) $(← arr (← lis.mapM (ofLi tms))))
  | .code info lang _ strs => do
    let str := strs.toList |> String.join
    if info.isEmpty && lang.isEmpty then
      ``(Doc.Block.code $(quote str))
    else
      let msg : MessageData :=
        "Info and language information in code blocks is not supported:" ++
        indentD m!"info is {repr info} and language is {repr lang}"
      throwError msg
  | .blockquote bs => do
    ``(Doc.Block.blockquote $(← arr (← bs.mapM (ofBlock tms))))
  | b => throwError "Unsupported block {repr b}"

  ofLi (tms : HashMap String Highlighted) : MD4Lean.Li MD4Lean.Block → PartElabM Term
  | {isTask, taskChar:=_, taskMarkOffset:=_, contents} => do
    if isTask then throwError "Tasks not supported"
    ``(Doc.ListItem.mk $(← arr (← contents.mapM (ofBlock tms))))

  ofInline (tms : HashMap String Highlighted) : MD4Lean.Text → PartElabM Term
  | .normal str => ``(Inline.text $(quote str))
  | .nullchar => throwError "Unsupported null character in Markdown"
  | .softbr txt => ``(Inline.linebreak $(quote txt))
  | .a href _title _isAuto contents => do
    let href := (← href.mapM ofAttrText).toList |> String.join
    let contents ← contents.mapM (ofInline tms)
    ``(Inline.link $(← arr contents) $(quote href))
  | .code str => do
    let codeStr := String.join str.toList
    if let some hl := tms[codeStr]? then
      ``(Inline.other (InlineExt.highlightedCode codeOpts $(quote hl)) #[])
    else
      ``(Inline.code $(quote <| String.join str.toList))
  | .em txt => do ``(Inline.emph $(← arr (← txt.mapM (ofInline tms))))
  | .strong txt => do ``(Inline.bold $(← arr (← txt.mapM (ofInline tms))))
  | .img src _title alt => do
    let mut src := (← src.mapM ofAttrText).toList |> String.join
    for (pat, template) in rewriter do
      if let some ρ := Pat.match pat src then
        src := ""
        for t in template do
          match t.subst ρ with
          | .error e => throwError e
          | .ok v => src := src ++ v
        break
    let alt := (alt.map inlineText).toList |> String.join
    ``(Inline.image $(quote alt) $(quote src))
  | .latexMath strs =>
    let str := strs.toList |> String.join
    ``(Inline.math MathMode.inline $(quote str))
  | .latexMathDisplay strs =>
    let str := strs.toList |> String.join
    ``(Inline.math MathMode.display $(quote str))
  | other => throwError "Unimplemented {repr other}"

  inlineText : MD4Lean.Text → String
  | .normal str
  | .softbr str => str
  | .em xs
  | .strong xs
  | .a _ _ _ xs => xs.map inlineText |>.toList |> String.join
  | _ => ""

  ofAttrText : MD4Lean.AttrText → PartElabM String
  | .normal txt => pure txt
  | other => throwError "Unimplemented {repr other}"



open Verso Doc Concrete in
open Lean Elab Command in
open PartElabM in
def elabAnalysisPage (x : Ident) (mod : Ident) (config : LitPageConfig) (title : StrLit) (genre : Term) (metadata? : Option Term) (rw : Option (TSyntax ``rewrites)) : CommandElabM Unit :=
  withTraceNode `verso.blog.literate (fun _ => pure m!"Literate '{title.getString}'") do

  let rewriter ← rw.mapM fun
    | `(rewrites|rewriting $[| $cases]*) => cases.mapM Internal.getSubst
    | rw => panic! s!"Unknown rewriter {rw}"
  let rewriter := rewriter.getD #[]

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let items ← withTraceNode `verso.blog.literate.loadMod (fun _ => pure m!"Loading '{mod}'") <|
    loadModuleContent mod.getId.toString

  let g ← runTermElabM fun _ => Term.elabTerm genre (some (.const ``Doc.Genre []))

  let ((), _st, st') ← liftTermElabM <| PartElabM.run genre g {} initState <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
    if let some metadata := metadata? then
      modifyThe PartElabM.State fun st => {st with partContext.metadata := some metadata}

    withTraceNode `verso.blog.literate.renderMod (fun _ => pure m!"Rendering '{mod}'") <|
      docFromModAndTerms config items rewriter


  let finished := st'.partContext.toPartFrame.close 0
  let finished :=
    -- Obey the Markdown convention of a single top-level header being the title of the document, if it's been followed
    if let .mk _ _ _ metadata #[] #[p] _ := finished then
      match p with
      | .mk t1 t2 t3 _ bs ps pos =>
        -- Propagate metadata fields
        FinishedPart.mk t1 t2 t3 metadata bs ps pos
      | _ => p
    else finished

  elabCommand <| ← `(def $x : Part $genre := $(← finished.toSyntax' genre))

open Verso.Genre.Blog.Literate in
open Lean.Parser.Tactic in
/--
Creates a page from a literate Lean module with Markdown module docstrings in it, performing a
best-effort conversion from a large subset of Markdown to Verso documents. Inline code elements are
elaborated as terms after the module itself; if they succeed, then they are highlighted as well. If
not, they become ordinary Markdown code.

Specifically, `def_literate_page PAGE from MOD in DIR as TITLE` defines a page `PAGE` by elaborating
the module `MOD` in the project directory `DIR` with title `TITLE`.

The literate Lean module does not need to use the same toolchain as Verso. `DIR` should be a project
directory that contains a toolchain file and a Lake configuration (`lakefile.toml` or
`lakefile.lean`), which should depend on the same version of SubVerso that Verso is using.

Set the option `verso.literateMarkdown.logInlines` to `true` to see the error messages that
prevented elaboration of inline elements.
-/
syntax "analysis_page " ident optConfig " from " ident "  as " str (" with " term)? (rewrites)? : command

open Verso Doc in
open Lean Elab Command in
open Verso.Genre.Blog Literate in
elab_rules : command
  | `(analysis_page $x $cfg:optConfig from $mod as $title $[with $metadata]? $[$rw:rewrites]?) => do
    let (config, _) ← liftTermElabM <| do
      litPageConfig cfg |>.run {elaborator := `x} |>.run {goals := []}
    withScope (fun sc => {sc with opts := Elab.async.set sc.opts false}) do
      let genre ← `(Page)
      elabAnalysisPage x mod config title genre metadata rw
