import RMQ.Headlines.RMQ

/-!
# RMQ paper import root

This is the narrow public Lean root for the RMQ paper artifact. It imports only
the canonical RMQ-facing headline aliases in `RMQ.Headlines.RMQ`. The
construction-facing capstone there combines the canonical reviewer payload and
canonical global trace with the uniform `76` certificate. The aggregate
`RMQ.Headlines` barrel remains available for the full repository, including the
explicit `RMQ.Headlines.RMQCompatibility` history module and standalone
rank/select and BP-navigation spoke surfaces.
-/
