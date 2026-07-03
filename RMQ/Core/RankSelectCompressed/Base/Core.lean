import RMQ.Core.RankSelectCompressed.Base.Core.RouteTables

/-!
# Core compressed/FID base barrel

This stable role barrel re-exports:

- `Core.Auxiliary` for compressed auxiliary directories and ambient block
  composition interfaces;
- `Core.TableBacked` for the simple table-backed FID layer;
- `Core.LocalRRR` for universal fixed-weight decode tables and local
  computed-RRR block kernels;
- `Core.RouteTables` for ambient computed-RRR route metadata and route-table
  families.

Public names remain in `RMQ.RankSelectSpec`.
-/
