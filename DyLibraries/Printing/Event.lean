module

public import DyLibraries.Printing.Basic
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState

namespace DY.Printing

public section

/-- A diagram annotation records the endpoints of the next message in a diagnostic run. -/
structure SendFromTo where
  sender : Participant
  receiver : Participant
  deriving DecidableEq

/-- Diagram annotations impose no security obligations on the protocol. -/
instance [ExecTraceTypes] [ProofTraceTypes] : ProtocolEvent.EventInv SendFromTo where
  invariant _ _ := True

/-- Encode endpoint names as JSON, including quotes, backslashes, and control characters. -/
instance [BytesFunctor] : PayloadPrinter SendFromTo where
  tag := "DY.Lib.Printing.DebugEvent"
  render _ e := (Lean.Json.mkObj [("sender", Lean.toJson e.sender), ("receiver", Lean.toJson e.receiver)]).compress
  principal e := e.sender

end
end DY.Printing
