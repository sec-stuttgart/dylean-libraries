module

public import DY.Trace.Invariant
import all DY.Trace.Invariant

namespace DY.Database
public section

-- TODO: Move this general trace-invariant helper to DY.Trace.Invariant in core.
/-- Every prefix of a trace satisfying its invariant also satisfies that invariant. -/
theorem traceInvariant_before
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  (before after : ProofTrace) :
  before ≤ after → after.Invariant → before.Invariant
:= by
  intro h hinv i hi
  have hl := Trace.length_le before after h
  have he := Trace.at_le before after i hi h
  have hp := Trace.le_imp_prefix_le_length_eq before after i h (by omega)
  simpa [he, hp] using hinv i (by omega)

end
end DY.Database
