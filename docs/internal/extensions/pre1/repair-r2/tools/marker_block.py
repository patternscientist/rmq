# Generates the PRE-1-R2 verdict-marker command text for a typed consumer.
BS = chr(92)


def marker_command(witness, guards_expr, marker, stage_style=False):
    lines = []
    A = lines.append
    A("open Lean Elab Command in")
    A("#eval show CommandElabM Unit from do")
    A("  -- (1) Whole file: elaborate this file again in this process from its own")
    A("  -- source text, with only this command blanked (line breaks kept), and read")
    A("  -- the message log of the header and of every command.")
    A("  let context ← read")
    A("  let source := context.fileMap.source")
    A("  let scope ← getScope")
    A("  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)")
    A("    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,")
    A("      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos")
    A("  let blank := (source.extract context.cmdPos markerStop).map")
    A("    fun c => if c == '" + BS + "n' || c == '" + BS + "r' then c else ' '")
    A("  let input := Parser.mkInputContext")
    A("    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)")
    A("    context.fileName")
    A("  let (header, parserState, headerMessages) ← Parser.parseHeader input")
    A("  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true")
    A("  let (headerEnv, headerMessages) ← processHeader header options headerMessages input")
    A("    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)")
    A("    (mainModule := (← getEnv).mainModule)")
    A("  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)")
    A("  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors")
    if witness is None:
        A("  if fileClean then IO.println \"%s\"" % marker)
        return "\n".join(lines) + "\n"
    A("  -- (2) The witness exists and collects no `sorryAx`.")
    A("  let witness := `%s" % witness)
    A("  let witnessClean ← if (← getEnv).contains witness then")
    A("      pure !((← collectAxioms witness).contains ``sorryAx)")
    A("    else pure false")
    if stage_style:
        A("  -- (3) The fixture checks hold; the two existing failure diagnostics stay.")
        A("  if !witnessClean then")
        A("    logError \"PRE1-STAGE-TYPED-CONSUMERS FAIL: a declaration is missing or depends on sorry\"")
        A("  else if !stageGuards then")
        A("    logError \"PRE1-STAGE-TYPED-CONSUMERS FAIL: an executable fixture check is false\"")
        A("  else if fileClean then")
        A("    IO.println \"%s\"" % marker)
        return "\n".join(lines) + "\n"
    if guards_expr:
        A("  -- (3) The guards hold.")
        A("  if fileClean && witnessClean && %s then IO.println \"%s\"" % (guards_expr, marker))
    else:
        A("  if fileClean && witnessClean then IO.println \"%s\"" % marker)
    return "\n".join(lines) + "\n"
