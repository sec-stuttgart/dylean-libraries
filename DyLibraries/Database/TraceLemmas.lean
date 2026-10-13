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
  intro h
  induction h with
  | equal => exact id
  | extend after entry h ih =>
    intro hinv
    exact ih hinv.1

end
end DY.Database
