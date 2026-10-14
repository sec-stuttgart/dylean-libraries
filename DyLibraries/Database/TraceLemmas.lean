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
  have he := Trace.at_le before after i hi h
  have hp := Trace.le_imp_prefix_le_length_eq before after i h (by omega)
  rw [he, hp]
  exact hinv i _

end
end DY.Database
