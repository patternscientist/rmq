import RMQ.Core.RankSelectCompressed.Base.ClassLengthEnvelope

/-!
# Compressed/FID rank-select base barrel

This stable import root re-exports the role-split fixed-weight compressed/FID
base construction layers:

- `Base.Core` for compressed auxiliary data, ambient block composition, and
  basic computed-RRR route-table families;
- `Base.DecodedRoutes` for decoded/packed route-table data and route-field
  table families;
- `Base.LogChunks` for log-chunk block arithmetic, route-width obstructions,
  and chunk route exactness facts;
- `Base.ClassLengthEnvelope` for concrete class/length metadata tables,
  route-field layouts, and route/class-length envelope families.

Public theorem names remain in `RMQ.RankSelectSpec`; this file is kept as the
compatibility import root for downstream modules.
-/
