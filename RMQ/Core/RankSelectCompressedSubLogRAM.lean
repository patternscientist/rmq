import RMQ.Core.RankSelectCompressedSubLogRAM.BoundedProfile

/-!
# Word-RAM replay barrel for sub-log compressed/FID rank/select

This stable import root re-exports the role-split replay modules:

- `RankSelectCompressedSubLogRAM.AccessRank` for interpreted access/rank
  reads and per-query execution stories;
- `RankSelectCompressedSubLogRAM.Select` for packed-Clark select replay;
- `RankSelectCompressedSubLogRAM.GlobalStore` for shared target/global payload
  stores;
- `RankSelectCompressedSubLogRAM.BoundedProfile` for trace-local event bounds
  and the interpreted compressed/FID profile.

Public theorem names remain in `RMQ.RankSelectSpec` and `RMQ.RankSelect`.
-/
