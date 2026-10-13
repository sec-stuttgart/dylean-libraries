module

import Examples.Login.Reachability
import Examples.Login.Printing
public meta import Examples.Login.Printing
import all Examples.Login.Specification
import all Examples.Login.Reachability
import all DY.Trace.Monad

namespace DY.Example.Login

open DY.Communication

/-- Run all three roles using separately stored, matching credentials. -/
def successfulLogin : Traceful Bool := do
  let (clientKeys, serverKeys) ← initializeKeys "Alice" "Server"
  let (clientState, serverState) ← provision "Alice" "Server"
  let (request, metadata) ← Client.start "Alice" clientState clientKeys
  let response ← Server.authenticate "Server" serverState serverKeys request
  let _ ← Client.finish "Alice" metadata response
  return true

#guard (successfulLogin.run Trace.nil).fst = some true

/-- Inspect with `#eval IO.print successfulLoginTrace`, or run `lake exe loginTrace`. -/
def successfulLoginTrace : String := loginTraceToString (successfulLogin.run Trace.nil).snd.val

#guard (Printing.traceToJson entryPrinter loginPrinters (successfulLogin.run Trace.nil).snd.val).length = (successfulLogin.run Trace.nil).snd.val.length
#guard (Printing.traceToJson entryPrinter loginPrinters (successfulLogin.run Trace.nil).snd.val).all (fun j => (_root_.Lean.Json.parse j.compress).toOption == some j)

-- The optional decoder recognizes a typed wire message and rejects raw bytes.
def printableRequest : WireMessage Payload := .request {request := {kind := "request", client := "Alice", secret := Literal.literalToBytes "password".toUTF8}, key := Literal.literalToBytes "key".toUTF8}

#guard loginPrinters.messageToString (Comparse.serialize printableRequest) = some (Printing.payloadToString loginPrinters printableRequest)
#guard loginPrinters.messageToString (Literal.literalToBytes ByteArray.empty) = none
#guard loginPrinters.message (Literal.literalToBytes ByteArray.empty) = "\"\""

-- Caller overrides propagate into enclosing core and request/response messages.
def customMessagePrinters : MessagePrinters Payload := { requestMessage := fun _ _ => "custom request", associatedData := fun _ _ => "custom identities" }

#guard messageDecoder loginPrinters (Comparse.serialize printableRequest) customMessagePrinters.wireMessage = some "custom request"
#guard messageDecoder loginPrinters (Comparse.serialize (.unsigned "Alice" "Server" printableRequest : EncryptionInput (WireMessage Payload))) customMessagePrinters.encryptionInput = some "sender=Alice, receiver=Server, payload=(custom request)"
#guard messageDecoder loginPrinters (Comparse.serialize ({client := none, server := "Server"} : AssociatedData)) customMessagePrinters.associatedData = some "custom identities"
#guard messageDecoder loginPrinters (Literal.literalToBytes ByteArray.empty) customMessagePrinters.wireMessage = none

/-- A different provisioned password cannot pass the server's comparison. -/
def wrongPassword : Traceful Nat := do
  let (clientKeys, serverKeys) ← initializeKeys "Alice" "Server"
  let (clientState, _) ← provision "Alice" "Server"
  let (_, serverState) ← provision "Alice" "Server"
  let (request, _) ← Client.start "Alice" clientState clientKeys
  Server.authenticate "Server" serverState serverKeys request

#guard (wrongPassword.run Trace.nil).fst = none

-- Failure still exposes a nonempty, serializable execution prefix.
#guard !(loginTraceToString (wrongPassword.run Trace.nil).snd.val).isEmpty
#guard (Printing.traceToJson entryPrinter loginPrinters (wrongPassword.run Trace.nil).snd.val).all (fun j => (_root_.Lean.Json.parse j.compress).toOption == some j)

/-- The server checks the claimed client even when the password matches. -/
def wrongClient : Traceful Nat := do
  let (clientKeys, serverKeys) ← initializeKeys "Alice" "Server"
  let (clientState, serverState) ← provision "Alice" "Server"
  let credentials : Credentials ← PersistentLocalState.getLocalState "Alice" clientState
  let (request, _) ← sendRequest clientKeys "Mallory" "Server" ({kind := "request", client := "Mallory", secret := credentials.password} : Payload)
  Server.authenticate "Server" serverState serverKeys request

#guard (wrongClient.run Trace.nil).fst = none

/-- Responses are bound to the original client's communication state. -/
def wrongRecipient : Traceful Bytes := do
  let (clientKeys, serverKeys) ← initializeKeys "Alice" "Server"
  let (clientState, serverState) ← provision "Alice" "Server"
  let (request, metadata) ← Client.start "Alice" clientState clientKeys
  let response ← Server.authenticate "Server" serverState serverKeys request
  Client.finish "Mallory" metadata response

#guard (wrongRecipient.run Trace.nil).fst = none

/-- Compromising either endpoint's credential handle publishes its stored password. -/
def credentialDisclosure
  (compromiseClient : Bool) :
  Traceful Bool
:= do
  let (clientState, serverState) ← provision "Alice" "Server"
  let credentials : Credentials ← PersistentLocalState.getLocalState "Alice" clientState
  let stateHandle := if compromiseClient then clientState else serverState
  let owner := if compromiseClient then "Alice" else "Server"
  let messageHandle ← compromiseCredentials stateHandle
  let disclosed ← Network.receiveMessage messageHandle
  let leaked : PersistentLocalState.LocalState Credentials ← Comparse.parse disclosed
  pure (leaked.participant == owner && leaked.state == credentials)

#guard (credentialDisclosure true |>.run Trace.nil).fst = some true
#guard (credentialDisclosure false |>.run Trace.nil).fst = some true
#guard (compromiseCredentials 0 |>.run Trace.nil).fst = none
#guard (Printing.traceToJson entryPrinter loginPrinters (credentialDisclosure true |>.run Trace.nil).snd.val).all (fun j => (_root_.Lean.Json.parse j.compress).toOption == some j)

end DY.Example.Login
