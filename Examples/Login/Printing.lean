module

public import Login.Specification
public import DyLibraries.Communication.Printing
import all Login.Specification

namespace DY.Example.Login
open Printing Communication

public section

#combine +toplevel into BytesPrinter from Random, Literal, Concat, PublicKeyEncryption, Signature, AEAD

def loginPayloadToString (b : Bytes → String) (x : Payload) : String := match x.kind with
  | "request" => s!"LoginRequest(client={x.client}, password=({b x.secret}))"
  | "cookie" => s!"LoginCookie(client={x.client}, cookie=({b x.secret}))"
  | _ => s!"LoginPayload(kind={x.kind}, client={x.client}, secret=({b x.secret}))"

instance : PayloadPrinter Payload where
  tag := "Login.Payload"
  render := loginPayloadToString
  principal x := x.client

instance : PayloadPrinter Credentials where
  tag := "Login.Credentials"
  render b x := s!"client={x.client}, server={x.server}, password=({b x.password})"

instance : PayloadPrinter LoginEvent where
  tag := "Login"
  render b
    | .provisioned client server password => s!"provisioned(client={client}, server={server}, password=({b password}))"
    | .started client server password => s!"started(client={client}, server={server}, password=({b password}))"
    | .authenticated client server password cookie => s!"authenticated(client={client}, server={server}, password=({b password}), cookie=({b cookie}))"
    | .cookieReceived client server cookie => s!"cookieReceived(client={client}, server={server}, cookie=({b cookie}))"
  principal
    | .provisioned client _ _ | .started client _ _ | .cookieReceived client _ _ => client
    | .authenticated _ server _ _ => server

#combine +toplevel into entryPrinter from Network, Random, ProtocolEvent LoginEvent, ProtocolEvent (CoreEvent (WireMessage Payload)), ProtocolEvent (RequestResponseEvent Payload), LongTermKeys (pkeKeyName (WireMessage Payload)), LongTermKeys (signatureKeyName (WireMessage Payload)), PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload), PersistentLocalState.CompromisableState Credentials

/-- Customize the application payload once; enclosing communication printers reuse it. -/
def loginMessagePrinters : MessagePrinters Payload := { payload := loginPayloadToString }

def loginPkePrinter : PartialBytesPrinter PublicKeyEncryption.Ciphertext.SubF := fun {publicKey, nonce, message} rec =>
  let plaintext := match messageDecoder defaultPrinters message loginMessagePrinters.encryptionInput with
    | some text => text
    | none => rec message
  s!"PkeEnc(pk=({rec publicKey}), nonce=({rec nonce}), msg=({plaintext}))"

def loginAeadPrinter : PartialBytesPrinter AEAD.Ciphertext.SubF := fun {key, nonce, message, associatedData} rec =>
  let plaintext := match messageDecoder defaultPrinters message loginMessagePrinters.payload with
    | some text => text
    | none => rec message
  let ad := match messageDecoder defaultPrinters associatedData loginMessagePrinters.associatedData with
    | some text => text
    | none => rec associatedData
  s!"AeadEnc(key=({rec key}), nonce=({rec nonce}), msg=({plaintext}), ad=({ad}))"

/-- Keep symbolic cryptographic wrappers, but decode their Login plaintext fields. -/
def loginBytesPrinter : PartialBytesPrinter BytesF := Bytes.PartialFunction.combine fun
  | 0 => Random.SubF.printing
  | 1 => Literal.SubF.printing
  | 2 => Concat.SubF.printing
  | 3 => PublicKeyEncryption.SubF.printing loginPkePrinter
  | 4 => Signature.SubF.printing
  | 5 => AEAD.SubF.printing loginAeadPrinter

def loginBytesToString (b : Bytes) : String := b.rec loginBytesPrinter

def loginPrinters : Printers :=
  let printers : Printers := { bytesToString := loginBytesToString }
  { printers with messageToString := fun b => messageDecoder printers b loginMessagePrinters.wireMessage }

def loginTraceToString (tr : ExecTrace) : String := traceToString entryPrinter loginPrinters tr

end
end DY.Example.Login
