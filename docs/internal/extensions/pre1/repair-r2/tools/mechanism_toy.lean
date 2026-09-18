import Lean

namespace MechProbe

theorem ok1 : 1 + 1 = 2 := rfl
theorem ok2 : ∀ n : Nat, n + 0 = n := fun _ => rfl
example : Nat := 3
#guard 1 + 1 = 2
--INJECT--

def consumerWitness : Unit :=
  let _ := @ok1
  let _ := @ok2
  --WITNESS--
  ()

def consumerGuards : Bool := decide (2 + 2 = 4)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos) context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true) (mainModule := (← getEnv).mainModule)
  let elaborated ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !elaborated.commandState.messages.hasErrors
  let witness := `MechProbe.consumerWitness
  let witnessClean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  IO.println s!"DIAG fileClean={fileClean} witnessClean={witnessClean} guards={consumerGuards} nestedErrors={(elaborated.commandState.messages.toList.filter (·.severity matches .error)).length}"
  if fileClean && witnessClean && consumerGuards then IO.println "MECH-PROBE PASS"

--TRAILER--
end MechProbe
