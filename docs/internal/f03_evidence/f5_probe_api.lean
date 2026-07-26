import Lean
open Lean

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

run_cmd do
  let env <- Lean.getEnv
  let mut hits : Array Name := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Lean.IR." then
      if hasSub s "sed" || hasSub s "ollect" || hasSub s "eps" then
        hits := hits.push n
    if s.startsWith "Lean.Compiler.LCNF.get" then hits := hits.push n
  Lean.logInfo m!"{hits.toList.take 80}"
