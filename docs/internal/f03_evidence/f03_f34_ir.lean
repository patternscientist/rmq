import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Compiler-IR erasure check: after erasure, does the executed code of the
controller's rank leaf still mention the two overhead constants?
-/

open Lean

def irMentions (n : Name) : CoreM Unit := do
  let env <- getEnv
  let mut found := false
  for (nm, d) in Lean.IR.declMapExt.getState env do
    if n.isPrefixOf nm then
      found := true
      let s := toString (format d)
      let hasBlock := (s.splitOn "RankBlockOverhead").length - 1
      let hasSuper := (s.splitOn "RankSuperOverhead").length - 1
      IO.println s!"IR decl {nm}: blockOverheadOccurrences={hasBlock} superOverheadOccurrences={hasSuper} irSize={s.length}"
  if !found then
    IO.println s!"NO IR DECL for prefix {n}"

open Lean Elab in
run_cmd Command.liftCoreM do
  irMentions `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  irMentions `RMQ.SuccinctFinal.WholeQueryInstr.evalGlobalWordTraceWithStore
  irMentions `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  irMentions `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  -- positive control: the store construction really does contain them
  irMentions `RMQ.BPNavigation.concreteBPCloseNavigationGlobalReadStore
  irMentions `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData
