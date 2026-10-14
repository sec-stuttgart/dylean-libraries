module

public import DyLibraries.Printing.Bytes
public import DY.Actions.LongTermKeys

namespace DY
open Printing
open _root_.Lean (toJson)

public section

def Network.entryPrinter [BytesFunctor] : EntryPrinter Network.ExecEntryT := fun p _ e => ⟨"Message", [("Content", toJson (p.message e.msg))]⟩

/-- Execution traces erase usage annotations. Null means unavailable, not NoUsage. -/
def Random.entryPrinter [BytesFunctor] : EntryPrinter Random.ExecEntryT := fun _ _ _ => ⟨"Nonce", [("Usage", .null)]⟩

def ProtocolEvent.entryPrinter [BytesFunctor] (EventT : Type) [PayloadPrinter EventT] : EntryPrinter (ProtocolEvent.ExecEntryT EventT) := fun p _ e => ⟨"Event", [("Principal", toJson (PayloadPrinter.principal e.ev)), ("Tag", toJson (PayloadPrinter.tag (α := EventT))), ("Content", toJson (payloadToString p e.ev))]⟩

namespace PersistentGlobalState

def State.entryPrinter [BytesFunctor] (StateT : Type) [PayloadPrinter StateT] : EntryPrinter (State.ExecEntryT StateT) := fun p i e => ⟨"Session", [("SessionID", toJson i), ("Principal", toJson (PayloadPrinter.principal e.st)), ("Tag", toJson (PayloadPrinter.tag (α := StateT))), ("Content", toJson (payloadToString p e.st))]⟩

instance [BytesFunctor] {StateT : Type} [PayloadPrinter StateT] : PayloadPrinter (Compromise.CompromiseEvent StateT) where
  tag := "Compromise." ++ PayloadPrinter.tag (α := StateT)
  render bytes e := PayloadPrinter.render bytes e.state
  principal e := PayloadPrinter.principal e.state

namespace Compromise
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from ProtocolEvent (CompromiseEvent StateT)
end Compromise

namespace CompromisableState
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from State StateT, Compromise StateT
end CompromisableState

end PersistentGlobalState

namespace PersistentLocalState

instance [BytesFunctor] {StateT : Type} [PayloadPrinter StateT] : PayloadPrinter (LocalState StateT) where
  tag := PayloadPrinter.tag (α := StateT)
  render bytes st := PayloadPrinter.render bytes st.state
  principal st := st.participant

namespace State
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from PersistentGlobalState.State (LocalState StateT)
end State

namespace Compromise
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from PersistentGlobalState.Compromise (LocalState StateT)
end Compromise

namespace CompromisableState
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from State StateT, Compromise StateT
end CompromisableState

end PersistentLocalState

namespace LongTermKeys

instance [BytesFunctor] (name : String) : PayloadPrinter (SecretKeyState name) where
  tag := "SecretKey." ++ name
  render bytes st := bytes st.sk

instance [BytesFunctor] (name : String) : PayloadPrinter (PublicKeyState name) where
  tag := "PublicKey." ++ name
  render bytes st := bytes st.pk
  principal st := st.p

#combine (name : String) into entryPrinter from PersistentLocalState.CompromisableState (SecretKeyState name), PersistentGlobalState.CompromisableState (PublicKeyState name)

end LongTermKeys

end
end DY
