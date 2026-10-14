module

public import DyLibraries.Printing.Trace
public import DyLibraries.Communication.All

namespace DY.Communication
open Printing

public section
variable [BytesFunctor]

def optionalParticipant (p : Option Participant) : String := p.getD "none"

instance [PayloadPrinter α] : PayloadPrinter (CommunicationMessage α) where
  tag := "CommunicationMessage"
  render b x := s!"sender={x.sender}, receiver={x.receiver}, payload=({PayloadPrinter.render b x.payload})"
  principal x := x.sender

instance [PayloadPrinter α] : PayloadPrinter (EncryptionInput α) where
  tag := "EncryptionInput"
  render b
    | .unsigned sender receiver payload => s!"sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload})"
    | .signed sender receiver payload => s!"sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload})"

instance [PayloadPrinter α] : PayloadPrinter (SignatureInput α) where
  tag := "SignatureInput"
  render b
    | .plain sender receiver payload => s!"plain(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .encrypted payload publicKey => s!"encrypted(payload=({b payload}), publicKey=({b publicKey}))"

instance : PayloadPrinter SignedCommunicationMessage where
  tag := "SignedCommunicationMessage"
  render b x := s!"message=({b x.message}), signature=({b x.signature})"

instance [PayloadPrinter α] : PayloadPrinter (RequestMessage α) where
  tag := "RequestMessage"
  render b x := s!"request=({PayloadPrinter.render b x.request}), key=({b x.key})"

instance : PayloadPrinter ResponseEnvelope where
  tag := "ResponseEnvelope"
  render b x := b x.ciphertext

instance : PayloadPrinter AssociatedData where
  tag := "AssociatedData"
  render _ x := s!"client={optionalParticipant x.client}, server={x.server}"

instance [PayloadPrinter α] : PayloadPrinter (WireMessage α) where
  tag := "WireMessage." ++ PayloadPrinter.tag (α := α)
  render b
    | .signature x => PayloadPrinter.render b x
    | .request x => PayloadPrinter.render b x
    | .response x => PayloadPrinter.render b x

instance [PayloadPrinter α] : PayloadPrinter (CommunicationMetadata α) where
  tag := "CommunicationMetadata"
  render b x := s!"client={optionalParticipant x.client}, server={x.server}, stateHandle={x.stateHandle}, request=({PayloadPrinter.render b x.request}), key=({b x.key})"

instance [PayloadPrinter α] : PayloadPrinter (AuthenticatedMetadata α) where
  tag := "AuthenticatedMetadata"
  render b x := PayloadPrinter.render b x.toMetadata

instance [PayloadPrinter α] : PayloadPrinter (ClientSendRequest α) where
  tag := "ClientSendRequest"
  render b x := s!"client={optionalParticipant x.client}, server={x.server}, request=({PayloadPrinter.render b x.request}), key=({b x.key})"

instance [PayloadPrinter α] : PayloadPrinter (ServerReceiveRequest α) where
  tag := "ServerReceiveRequest"
  render b x := s!"client={optionalParticipant x.client}, request=({PayloadPrinter.render b x.request}), key=({b x.key})"

instance [PayloadPrinter α] : PayloadPrinter (ClientReceiveResponse α) where
  tag := "ClientReceiveResponse"
  render b x := s!"server={x.server}, response=({PayloadPrinter.render b x.response}), key=({b x.key})"

instance [PayloadPrinter α] : PayloadPrinter (CommunicationState α) where
  tag := "CommunicationState." ++ PayloadPrinter.tag (α := α)
  render b
    | .clientSendRequest x => s!"clientSendRequest({PayloadPrinter.render b x})"
    | .serverReceiveRequest x => s!"serverReceiveRequest({PayloadPrinter.render b x})"
    | .clientReceiveResponse x => s!"clientReceiveResponse({PayloadPrinter.render b x})"

instance [PayloadPrinter α] : PayloadPrinter (CoreEvent α) where
  tag := "CoreEvent." ++ PayloadPrinter.tag (α := α)
  render b
    | .confidentialSend sender receiver payload => s!"confidentialSend(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .confidentialReceive sender receiver payload => s!"confidentialReceive(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .authenticatedSend sender receiver payload => s!"authenticatedSend(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .authenticatedReceive sender receiver payload => s!"authenticatedReceive(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .confidentialAuthenticatedSend sender receiver payload => s!"confidentialAuthenticatedSend(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
    | .confidentialAuthenticatedReceive sender receiver payload => s!"confidentialAuthenticatedReceive(sender={sender}, receiver={receiver}, payload=({PayloadPrinter.render b payload}))"
  principal
    | .confidentialSend sender _ _ => sender
    | .confidentialReceive _ receiver _ => receiver
    | .authenticatedSend sender _ _ => sender
    | .authenticatedReceive _ receiver _ => receiver
    | .confidentialAuthenticatedSend sender _ _ => sender
    | .confidentialAuthenticatedReceive _ receiver _ => receiver

instance [PayloadPrinter α] : PayloadPrinter (RequestResponseEvent α) where
  tag := "RequestResponseEvent." ++ PayloadPrinter.tag (α := α)
  render b
    | .clientSendRequest auth client server request key => s!"clientSendRequest(authentication={match auth with | .authenticated => "authenticated" | .unauthenticated => "unauthenticated"}, client={client}, server={server}, request=({PayloadPrinter.render b request}), key=({b key}))"
    | .serverReceiveRequest client server request key => s!"serverReceiveRequest(client={optionalParticipant client}, server={server}, request=({PayloadPrinter.render b request}), key=({b key}))"
    | .serverSendResponse client server request response key => s!"serverSendResponse(client={optionalParticipant client}, server={server}, request=({PayloadPrinter.render b request}), response=({PayloadPrinter.render b response}), key=({b key}))"
    | .clientReceiveResponse client response metadata => s!"clientReceiveResponse(client={client}, response=({PayloadPrinter.render b response}), metadata=({PayloadPrinter.render b metadata}))"
  principal
    | .clientSendRequest _ client _ _ _ => client
    | .serverReceiveRequest _ server _ _ => server
    | .serverSendResponse _ server _ _ _ => server
    | .clientReceiveResponse client _ _ => client

/-- Per-call printers for the core and request/response message types.
Defaults compose through the supplied payload, request, response, and wire printers. -/
structure MessagePrinters (α : Type) [PayloadPrinter α] where
  payload : (Bytes → String) → α → String := PayloadPrinter.render
  signedMessage : (Bytes → String) → SignedCommunicationMessage → String := PayloadPrinter.render
  requestMessage : (Bytes → String) → RequestMessage α → String := fun b x => s!"request=({payload b x.request}), key=({b x.key})"
  responseEnvelope : (Bytes → String) → ResponseEnvelope → String := PayloadPrinter.render
  associatedData : (Bytes → String) → AssociatedData → String := PayloadPrinter.render
  wireMessage : (Bytes → String) → WireMessage α → String := fun b x => match x with
    | .signature x => signedMessage b x
    | .request x => requestMessage b x
    | .response x => responseEnvelope b x
  encryptionInput : (Bytes → String) → EncryptionInput (WireMessage α) → String := fun b x => match x with
    | .unsigned sender receiver payload | .signed sender receiver payload => s!"sender={sender}, receiver={receiver}, payload=({wireMessage b payload})"
  signatureInput : (Bytes → String) → SignatureInput (WireMessage α) → String := fun b x => match x with
    | .plain sender receiver payload => s!"plain(sender={sender}, receiver={receiver}, payload=({wireMessage b payload}))"
    | .encrypted payload publicKey => s!"encrypted(payload=({b payload}), publicKey=({b publicKey}))"

/-- Decode a chosen type using an optional caller-supplied typed printer.
Parsing failure returns `none`, so the caller can retain symbolic rendering. -/
def messageDecoder [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [Comparse.ParseableSerializeable α] [PayloadPrinter α] (p : Printers) (b : Bytes) (printer : (Bytes → String) → α → String := PayloadPrinter.render) : Option String := do
  let x : α ← Comparse.parse b
  return printer p.bytesToString x

end
end DY.Communication

namespace DY.PersistentLocalUpdateableState
open Printing
open _root_.Lean (toJson)
public section

/-- Render the stable state ID separately from the trace entry's timestamp. -/
def State.entryPrinter
  [BytesFunctor] (StateT : Type) [PayloadPrinter StateT] :
  EntryPrinter (State.ExecEntryT StateT)
:=
  fun p _ e => ⟨"Session", [("SessionID", toJson e.stateId), ("Principal", toJson e.participant), ("Tag", toJson (PayloadPrinter.tag (α := StateT))), ("Content", toJson (payloadToString p e.state))]⟩

instance [BytesFunctor] {StateT : Type} [PayloadPrinter StateT] : PayloadPrinter (Compromise.CompromiseEvent StateT) where
  tag := "Compromise." ++ PayloadPrinter.tag (α := StateT)
  render bytes e := s!"stateId={e.stateId}, state=({PayloadPrinter.render bytes e.state})"
  principal e := e.participant

namespace Compromise
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from ProtocolEvent (CompromiseEvent StateT)
end Compromise

namespace CompromisableState
#combine (StateT : Type) [PayloadPrinter StateT] into entryPrinter from State StateT, Compromise StateT
end CompromisableState

end
end DY.PersistentLocalUpdateableState
