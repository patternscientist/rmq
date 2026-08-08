import VerifiedDS.UnionFind.Forest.Reference

/-!
# Union-find parent-forest barrel

This stable import root re-exports the role-split parent-forest development:

- `Forest.Base` for parent-pointer forests, invariants, ranked linking, and
  root-mass/rank-power preservation;
- `Forest.NoCompression` for no-compression union-by-rank states;
- `Forest.BackendOps` for full-compression backend operations and refinement;
- `Forest.Potentials` and `Forest.PotentialProofs` for rank/slack/Tarjan-style
  potential scaffolding;
- `Forest.Amortized` for representation/amortized backend packaging;
- `Forest.Reference` for the direct `State` adapter and public refinement
  checkpoint.

Public names remain in `VerifiedDS.UnionFind.Forest` and nested `ParentForest`
namespaces.
-/
