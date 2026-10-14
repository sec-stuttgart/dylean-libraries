module

public import DyLibraries.Printing
public meta import DyLibraries.Printing
import all DyLibraries.Printing.Basic
import all DY.ALaCarte.Basic

namespace DY.Printing.Test

#combine +toplevel into BytesFunctor, BytesLength, BytesPrinter from Random, Literal, Concat, PublicKeyEncryption, Signature, AEAD, Hash, DiffieHellman, KdfExtract, KdfExpand

def nonce : Bytes := ({timestamp := 7, size := 32} : Random.SubF Bytes).pack
def literal : Bytes := Literal.literalToBytes "hello".toUTF8

#guard bytesToString nonce = "Nonce #7"
#guard bytesToString literal = "\"hello\""
#guard literalToString ⟨#[0, 10, 34, 92, 127, 255]⟩ = "\"\\x00\\x0a\\\"\\\\\\x7f\\xff\""
#guard literalToString "é".toUTF8 = "\"\\xc3\\xa9\""
#guard bytesToString (({lhs := literal, rhs := nonce} : Concat.Concat.SubF Bytes).pack) = "[\"hello\",Nonce #7]"
#guard bytesToString (({sk := nonce} : PublicKeyEncryption.Pk.SubF Bytes).pack) = "Pk(sk=(Nonce #7))"
#guard bytesToString (({publicKey := nonce, nonce, message := literal} : PublicKeyEncryption.Ciphertext.SubF Bytes).pack) = "PkeEnc(pk=(Nonce #7), nonce=(Nonce #7), msg=(\"hello\"))"
#guard bytesToString (({sk := nonce} : Signature.Vk.SubF Bytes).pack) = "Vk(Nonce #7)"
#guard bytesToString (({sk := nonce, nonce, msg := literal} : Signature.Sign.SubF Bytes).pack) = "sig(sk=(Nonce #7), nonce=(Nonce #7), msg=(\"hello\"))"
#guard bytesToString (({key := nonce, nonce, message := literal, associatedData := literal} : AEAD.Ciphertext.SubF Bytes).pack) = "AeadEnc(key=(Nonce #7), nonce=(Nonce #7), msg=(\"hello\"), ad=(\"hello\"))"
#guard bytesToString (({input := nonce} : Hash.Hash.SubF Bytes).pack) = "Hash(Nonce #7)"
#guard bytesToString (({sk := nonce} : DiffieHellman.DhPk.SubF Bytes).pack) = "DhPub(sk=(Nonce #7))"
#guard bytesToString (({pk := literal, sk := nonce} : DiffieHellman.Dh.SubF Bytes).pack) = "Dh(sk=(Nonce #7), pk=(\"hello\"))"
#guard bytesToString (({salt := literal, ikm := nonce} : KdfExtract.KdfExtract.SubF Bytes).pack) = "KdfExtract(salt=(\"hello\"), ikm=(Nonce #7))"
#guard bytesToString (({prk := nonce, info := literal, len := 42} : KdfExpand.KdfExpand.SubF Bytes).pack) = "KdfExpand(prk=(Nonce #7), info=(\"hello\"), len=42)"

public instance : PayloadPrinter String where
  tag := "test\"\n"
  render _ s := s
  principal := id

#combine +toplevel into ExecEntryT, entryPrinter from Network, Random, ProtocolEvent String, PersistentLocalState.CompromisableState String

def sample : ExecTrace := Trace.nil.append ({length := 32} : Random.ExecEntryT) |>.append ({msg := nonce} : Network.ExecEntryT) |>.append ({ev := "Alice\"\n\\é"} : ProtocolEvent.ExecEntryT String)

#guard traceToString entryPrinter defaultPrinters Trace.nil = ""
#guard (traceToJson entryPrinter defaultPrinters sample).length = 3
#guard (traceToJson entryPrinter defaultPrinters sample).map (fun j => (j.getObjValAs? Nat "TraceID").toOption) = [some 0, some 1, some 2]
#guard (traceToJson entryPrinter defaultPrinters sample).all (fun j => (_root_.Lean.Json.parse j.compress).toOption == some j)
#guard ((traceToString entryPrinter defaultPrinters sample).splitOn "\n").length == 4
#guard (traceEntries sample).zipIdx.all (fun (e, i) => ((entryPrinter defaultPrinters i e).toJsonString i).startsWith "{\"TraceID\":")
#guard (traceEntries sample).zipIdx.all (fun (e, i) => (_root_.Lean.Json.parse ((entryPrinter defaultPrinters i e).toJsonString i)).toOption == some ((entryPrinter defaultPrinters i e).toJson i))
#guard (Printers.message {defaultPrinters with messageToString := fun _ => some "decoded"} nonce) = "decoded"
#guard (Printers.message {defaultPrinters with messageToString := fun _ => none} nonce) = "Nonce #7"

def stateAndCompromise : ExecTrace := Trace.nil.append ({st := {participant := "Alice", state := "state"}} : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState String)) |>.append ({ev := {state := {participant := "Alice", state := "state"}}} : ProtocolEvent.ExecEntryT (PersistentGlobalState.Compromise.CompromiseEvent (PersistentLocalState.LocalState String)))

#guard (traceToJson entryPrinter defaultPrinters stateAndCompromise).map (fun j => (j.getObjValAs? String "Type").toOption) = [some "Session", some "Event"]
#guard (traceToJson entryPrinter defaultPrinters stateAndCompromise).map (fun j => (j.getObjValAs? String "Principal").toOption) = [some "Alice", some "Alice"]
#guard (((traceToJson entryPrinter defaultPrinters stateAndCompromise)[0]!).getObjValAs? Nat "SessionID").toOption = some 0

end DY.Printing.Test
