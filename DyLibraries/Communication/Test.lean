module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.PublicKeyEncryption
public import DY.EquationalTheory.Sign
public import DY.EquationalTheory.AEAD
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState
public import DY.Actions.LongTermKeys
public import DY.Communication.All
import all DY.Communication.RequestResponse.Invariants
import all DY.Communication.Core
import all DY.Communication.RequestResponse
public meta import DY.Trace.Search
public meta import DY.Communication.Data
public meta import DY.EquationalTheory.Sign
public meta import DY.EquationalTheory.PublicKeyEncryption
public meta import DY.EquationalTheory.AEAD
import DY.Meta

import DY.Meta.Step

namespace DY.Communication.Test

open DY.Comparse

public structure Payload where
  value : String
deriving DecidableEq, Repr

public instance [BytesFunctor] [BytesLength]
    [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
    [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] :
    ParseableSerializeable Payload := .make <|
  .triviallyIsomorphic
    (.string)
    (fun value => { value })
    (fun payload => payload.value)

@[simp]
public theorem Payload.IsWellFormed_eq
    [BytesFunctor] [BytesLength]
    [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
    [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
    (pre : Bytes → τ → Prop) [BytesCompatibleTracePred pre]
    (payload : Payload) (tr : τ) : IsWellFormed pre payload tr := by
  simp [IsWellFormed, ParseableSerializeable.mf]

public instance : CoreConfig Payload where
  tag := "Communication.Test.Direct"

public instance : RequestResponseConfig Payload where
  tag := "Communication.Test.RequestResponse"

public section ExecutionConfiguration

public class HasExecBytes where
  [bytesFunctor : BytesFunctor]
  [random : BytesFunctor.Has Random.SubF]
  [literal : BytesFunctor.Has Literal.SubF]
  [concat : BytesFunctor.Has Concat.SubF]
  [pke : BytesFunctor.Has PublicKeyEncryption.SubF]
  [signature : BytesFunctor.Has Signature.SubF]
  [aead : BytesFunctor.Has AEAD.SubF]
  [bytesLength : BytesLength]
  [randomLength : BytesLength.Has Random.SubF.length]
  [literalLength : BytesLength.Has Literal.SubF.length]
  [concatLength : BytesLength.Has Concat.SubF.length]
  [pkeLength : BytesLength.Has PublicKeyEncryption.SubF.length]
  [signatureLength : BytesLength.Has Signature.SubF.length]
  [aeadLength : BytesLength.Has AEAD.SubF.length]
  [attackerKnowledge : AttackerKnowledge]
  [randomKnowledge : AttackerKnowledge.Has Random.attackerKnowledge]
  [literalKnowledge : AttackerKnowledge.Has Literal.attackerKnowledge]
  [concatKnowledge : AttackerKnowledge.Has Concat.attackerKnowledge]
  [pkeKnowledge : AttackerKnowledge.Has PublicKeyEncryption.attackerKnowledge]
  [signatureKnowledge : AttackerKnowledge.Has Signature.attackerKnowledge]
  [aeadKnowledge : AttackerKnowledge.Has AEAD.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunctor
attribute [reducible, scoped instance] HasExecBytes.random
attribute [reducible, scoped instance] HasExecBytes.literal
attribute [reducible, scoped instance] HasExecBytes.concat
attribute [reducible, scoped instance] HasExecBytes.pke
attribute [reducible, scoped instance] HasExecBytes.signature
attribute [reducible, scoped instance] HasExecBytes.aead
attribute [reducible, scoped instance] HasExecBytes.bytesLength
attribute [scoped instance] HasExecBytes.randomLength
attribute [scoped instance] HasExecBytes.literalLength
attribute [scoped instance] HasExecBytes.concatLength
attribute [scoped instance] HasExecBytes.pkeLength
attribute [scoped instance] HasExecBytes.signatureLength
attribute [scoped instance] HasExecBytes.aeadLength
attribute [reducible, scoped instance] HasExecBytes.attackerKnowledge
attribute [scoped instance] HasExecBytes.randomKnowledge
attribute [scoped instance] HasExecBytes.literalKnowledge
attribute [scoped instance] HasExecBytes.concatKnowledge
attribute [scoped instance] HasExecBytes.pkeKnowledge
attribute [scoped instance] HasExecBytes.signatureKnowledge
attribute [scoped instance] HasExecBytes.aeadKnowledge

public class HasExecTrace extends HasExecBytes where
  [execTraceTypes : ExecTraceTypes]
  [networkEntry : ExecTraceTypes.Has Network.ExecEntryT]
  [randomEntry : ExecTraceTypes.Has Random.ExecEntryT]
  [directCoreEvent : ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent Payload))]
  [rrCoreEvent : ExecTraceTypes.Has
    (ProtocolEvent.ExecEntryT (CoreEvent (WireMessage Payload)))]
  [rrEvent : ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent Payload))]
  [directPkeKeys : ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName Payload))]
  [directSignatureKeys : ExecTraceTypes.Has
    (LongTermKeys.ExecEntryT (signatureKeyName Payload))]
  [rrPkeKeys : ExecTraceTypes.Has
    (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage Payload)))]
  [rrSignatureKeys : ExecTraceTypes.Has
    (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage Payload)))]
  [communicationState : ExecTraceTypes.Has
    (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState Payload))]
  [baseAttackerKnowledge : BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.execTraceTypes
attribute [reducible, scoped instance] HasExecTrace.networkEntry
attribute [reducible, scoped instance] HasExecTrace.randomEntry
attribute [reducible, scoped instance] HasExecTrace.directCoreEvent
attribute [reducible, scoped instance] HasExecTrace.rrCoreEvent
attribute [reducible, scoped instance] HasExecTrace.rrEvent
attribute [reducible, scoped instance] HasExecTrace.directPkeKeys
attribute [reducible, scoped instance] HasExecTrace.directSignatureKeys
attribute [reducible, scoped instance] HasExecTrace.rrPkeKeys
attribute [reducible, scoped instance] HasExecTrace.rrSignatureKeys
attribute [reducible, scoped instance] HasExecTrace.communicationState
attribute [reducible, scoped instance] HasExecTrace.baseAttackerKnowledge

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

public instance : HasExecBytes where

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  Random,
  ProtocolEvent (CoreEvent Payload),
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName Payload),
  LongTermKeys (signatureKeyName Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),

public instance : HasExecTrace where

end ExecutionConfiguration

section ParsingTests

variable [HasExecBytes]

private def requestPayload : Payload := { value := "request" }
private def responsePayload : Payload := { value := "response" }

private def sampleRequest : WireMessage Payload :=
  .request { request := requestPayload, key := serialize ({ value := "key" } : Payload) }

private def sampleResponse : WireMessage Payload :=
  .response {
    nonce := serialize ({ value := "nonce" } : Payload)
    ciphertext := serialize ({ value := "ciphertext" } : Payload)
  }

example : (parse (serialize sampleRequest) : Option (WireMessage Payload)) =
    some sampleRequest := by simp

example : (parse (serialize sampleResponse) : Option (WireMessage Payload)) =
    some sampleResponse := by simp

example : (parse (serialize requestPayload) : Option Payload) = some requestPayload := by simp

#guard (parse (Comparse.BytesLike.empty : Bytes) : Option (WireMessage Payload)).isNone
#guard (parse (serialize sampleRequest) : Option ResponseEnvelope).isNone

private def testKey : Bytes := serialize ({ value := "key" } : Payload)
private def testNonce : Bytes := serialize ({ value := "nonce" } : Payload)
private def otherNonce : Bytes := serialize ({ value := "other nonce" } : Payload)
private def testMessage : Bytes := serialize responsePayload
private def testAD : Bytes := serialize ({ client := none, server := "server" } : AssociatedData)
private def otherAD : Bytes := serialize ({ client := some "client", server := "server" } : AssociatedData)

example : AEAD.decrypt testKey testNonce
    (AEAD.encrypt testKey testNonce testMessage testAD) testAD = some testMessage := by simp

#guard (AEAD.decrypt testKey otherNonce
  (AEAD.encrypt testKey testNonce testMessage testAD) testAD).isNone
#guard (AEAD.decrypt testKey testNonce
  (AEAD.encrypt testKey testNonce testMessage testAD) otherAD).isNone

private def testSecret : Bytes := serialize ({ value := "secret" } : Payload)
private def otherSecret : Bytes := serialize ({ value := "other secret" } : Payload)

example : PublicKeyEncryption.decrypt testSecret
    (PublicKeyEncryption.encrypt (PublicKeyEncryption.pk testSecret) testNonce testMessage) =
    some testMessage := by simp

#guard (PublicKeyEncryption.decrypt otherSecret
  (PublicKeyEncryption.encrypt (PublicKeyEncryption.pk testSecret) testNonce testMessage)).isNone
#guard !(Signature.verify (Signature.vk testSecret) testMessage
  (Signature.sign otherSecret testNonce testMessage))

end ParsingTests

section RuntimeTests

variable [HasExecTrace]

private def runtimeRequestPayload : Payload := { value := "request" }
private def runtimeResponsePayload : Payload := { value := "response" }

public def successfulCoreModes : Traceful Bool := do
  let (alice, bob) ← initializeCore (α := Payload) "Alice" "Bob"

  let confidentialHandle ← sendConfidential alice "Alice" "Bob" runtimeRequestPayload
  let confidential ← receiveConfidential bob "Bob" confidentialHandle
  guard (confidential = { sender := "Alice", receiver := "Bob", payload := runtimeRequestPayload })

  let authenticatedHandle ← sendAuthenticated alice "Alice" "Bob" runtimeRequestPayload
  let authenticated ← receiveAuthenticated bob "Bob" authenticatedHandle
  guard (authenticated = { sender := "Alice", receiver := "Bob", payload := runtimeRequestPayload })

  let bothHandle ← sendConfidentialAuthenticated alice "Alice" "Bob" runtimeRequestPayload
  let both ← receiveConfidentialAuthenticated bob "Bob" bothHandle
  guard (both = { sender := "Alice", receiver := "Bob", payload := runtimeRequestPayload })
  pure true

#guard (successfulCoreModes.run Trace.nil).fst = some true

public def successfulAnonymousRequestResponse : Traceful Bool := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, clientMetadata) ←
    sendRequest clientHandles "Alice" "Bob" runtimeRequestPayload
  let (receivedRequest, serverMetadata) ←
    receiveRequest serverHandles "Bob" requestHandle
  guard (receivedRequest = runtimeRequestPayload)
  let responseHandle ← sendResponse "Bob" serverMetadata runtimeResponsePayload
  let response ← receiveResponse (α := Payload) "Alice" clientMetadata responseHandle
  guard (response = runtimeResponsePayload)
  let replayed ← receiveResponse (α := Payload) "Alice" clientMetadata responseHandle
  guard (replayed = runtimeResponsePayload)
  pure true

#guard (successfulAnonymousRequestResponse.run Trace.nil).fst = some true

public def successfulAuthenticatedRequestResponse : Traceful Bool := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, clientMetadata) ←
    sendRequestAuthenticated clientHandles "Alice" "Bob" runtimeRequestPayload
  let (receivedRequest, serverMetadata) ←
    receiveRequestAuthenticated serverHandles "Bob" requestHandle
  guard (receivedRequest = runtimeRequestPayload)
  let .serverReceiveRequest received ← PersistentLocalUpdateableState.getLocalState (StateT := CommunicationState Payload) "Bob" serverMetadata | failure
  guard (received.client = some "Alice")
  let responseHandle ← sendResponse "Bob" serverMetadata runtimeResponsePayload
  let response ← receiveResponseAuthenticated (α := Payload) "Alice" clientMetadata responseHandle
  guard (response = runtimeResponsePayload)
  pure true

#guard (successfulAuthenticatedRequestResponse.run Trace.nil).fst = some true

public def wrongCoreReceiverFails : Traceful Unit := do
  let (alice, bob) ← initializeCore (α := Payload) "Alice" "Bob"
  let handle ← sendConfidential alice "Alice" "Bob" runtimeRequestPayload
  let _ ← receiveConfidential (α := Payload) bob "Mallory" handle

#guard (wrongCoreReceiverFails.run Trace.nil).fst = none

public def wrongCoreKeysFail : Traceful Unit := do
  let (alice, _) ← initializeCore (α := Payload) "Alice" "Bob"
  let (_, secondBob) ← initializeCore (α := Payload) "Mallory" "Bob"
  let handle ← sendConfidentialAuthenticated alice "Alice" "Bob" runtimeRequestPayload
  let _ ← receiveConfidentialAuthenticated (α := Payload) secondBob "Bob" handle

#guard (wrongCoreKeysFail.run Trace.nil).fst = none

public def malformedCoreMessageFails : Traceful Unit := do
  let (_, bob) ← initializeCore (α := Payload) "Alice" "Bob"
  let handle ← Network.sendMessage (Comparse.BytesLike.empty : Bytes)
  let _ ← receiveConfidential (α := Payload) bob "Bob" handle

#guard (malformedCoreMessageFails.run Trace.nil).fst = none

public def unknownServerStateFails : Traceful Unit := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, _) ←
    sendRequest (α := Payload) clientHandles "Alice" "Bob" runtimeRequestPayload
  let (_, serverMetadata) ← receiveRequest (α := Payload) serverHandles "Bob" requestHandle
  let badMetadata := serverMetadata + 1
  let _ ← sendResponse "Bob" badMetadata runtimeResponsePayload

#guard (unknownServerStateFails.run Trace.nil).fst = none

public def wrongParticipantFails : Traceful Unit := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, clientMetadata) ←
    sendRequest clientHandles "Alice" "Bob" runtimeRequestPayload
  let (_, serverMetadata) ← receiveRequest (α := Payload) serverHandles "Bob" requestHandle
  let responseHandle ← sendResponse "Bob" serverMetadata runtimeResponsePayload
  let _ ← receiveResponse (α := Payload) "Mallory" clientMetadata responseHandle

#guard (wrongParticipantFails.run Trace.nil).fst = none

public def unknownClientStateFails : Traceful Unit := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, clientMetadata) ←
    sendRequest clientHandles "Alice" "Bob" runtimeRequestPayload
  let (_, serverMetadata) ← receiveRequest (α := Payload) serverHandles "Bob" requestHandle
  let responseHandle ← sendResponse "Bob" serverMetadata runtimeResponsePayload
  let badMetadata := clientMetadata + 1
  let _ ← receiveResponse (α := Payload) "Alice" badMetadata responseHandle

#guard (unknownClientStateFails.run Trace.nil).fst = none

public def wrongStateVariantFails : Traceful Unit := do
  let (clientHandles, serverHandles) ←
    initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestHandle, clientMetadata) ←
    sendRequest clientHandles "Alice" "Bob" runtimeRequestPayload
  let (_, serverMetadata) ← receiveRequest (α := Payload) serverHandles "Bob" requestHandle
  let responseHandle ← sendResponse "Bob" serverMetadata runtimeResponsePayload
  let .clientSendRequest sent ← PersistentLocalUpdateableState.getLocalState (StateT := CommunicationState Payload) "Alice" clientMetadata | failure
  let wrongHandle ← PersistentLocalUpdateableState.newSessionId (CommunicationState Payload) "Alice"
  let _ ← PersistentLocalUpdateableState.setLocalState "Alice" wrongHandle
    (.clientReceiveResponse {
      server := "Bob", response := runtimeResponsePayload, key := sent.key
    } : CommunicationState Payload)
  let badMetadata := wrongHandle
  let _ ← receiveResponse (α := Payload) "Alice" badMetadata responseHandle

#guard (wrongStateVariantFails.run Trace.nil).fst = none

public def compromiseStateSucceeds : Traceful Bool := do
  let (clientHandles, _) ← initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (_, metadata) ← sendRequest clientHandles "Alice" "Bob" runtimeRequestPayload
  let compromiseHandle ← compromiseCommunicationState (α := Payload) "Alice" metadata
  let serializedState ← Network.receiveMessage compromiseHandle
  let localState : CommunicationState Payload ← parse serializedState
  match localState with
  | .clientSendRequest state =>
    guard (state.server = "Bob")
    guard (state.request = runtimeRequestPayload)
    pure true
  | _ => failure

#guard (compromiseStateSucceeds.run Trace.nil).fst = some true

/-- Multiple requests retain separate IDs even when responses arrive out of order. -/
public def independentRequestStates : Traceful Bool := do
  let (clientKeys, serverKeys) ← initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (firstMessage, firstClientId) ← sendRequest clientKeys "Alice" "Bob" ({ value := "first" } : Payload)
  let (secondMessage, secondClientId) ← sendRequest clientKeys "Alice" "Bob" ({ value := "second" } : Payload)
  guard (firstClientId ≠ secondClientId)
  let (firstRequest, firstServerId) ← receiveRequest (α := Payload) serverKeys "Bob" firstMessage
  let (secondRequest, secondServerId) ← receiveRequest (α := Payload) serverKeys "Bob" secondMessage
  guard (firstServerId ≠ secondServerId)
  let secondResponse ← sendResponse "Bob" secondServerId secondRequest
  let firstResponse ← sendResponse "Bob" firstServerId firstRequest
  let second ← receiveResponse (α := Payload) "Alice" secondClientId secondResponse
  let first ← receiveResponse (α := Payload) "Alice" firstClientId firstResponse
  let replay ← receiveResponse (α := Payload) "Alice" firstClientId firstResponse
  pure (first.value = "first" && second.value = "second" && replay = first)

#guard (independentRequestStates.run Trace.nil).fst = some true

/-- The authenticated response API rejects an anonymous request ID. -/
public def anonymousIdRejectedByAuthenticatedReceive : Traceful Payload := do
  let (clientKeys, serverKeys) ← initializeRequestResponse (α := Payload) "Alice" "Bob"
  let (requestMessage, clientId) ← sendRequest clientKeys "Alice" "Bob" runtimeRequestPayload
  let (_, serverId) ← receiveRequest (α := Payload) serverKeys "Bob" requestMessage
  let responseMessage ← sendResponse "Bob" serverId runtimeResponsePayload
  receiveResponseAuthenticated (α := Payload) "Alice" clientId responseMessage

#guard (anonymousIdRejectedByAuthenticatedReceive.run Trace.nil).fst = none

end RuntimeTests

section LabelChecks

variable [HasExecTrace]

example (participant : Participant) (stateId : Nat) (state : CommunicationState Payload) (tr : ExecTrace) :
    (PersistentLocalUpdateableState.label participant stateId state).isCorrupt tr =
      PersistentLocalUpdateableState.LocalStateCompromised participant stateId state tr :=
  PersistentLocalUpdateableState.label_isCorrupt _ _ _ _

example (participant : Participant) (tr : ExecTrace) :
    communicationStateCompromised (α := Payload) participant tr →
      (requestResponseParticipantLabel (α := Payload) participant).isCorrupt tr := by
  intro h
  rw [requestResponseParticipantLabel_isCorrupt]
  exact Or.inr h

end LabelChecks

public section ProofComposition

/-- The proof configuration intentionally covers the request/response layer.
The direct-core execution checks above share the byte algebra but do not add a
second, competing global PKE/signature predicate. -/
public class HasProofTrace extends HasExecTrace where
  [proofTraceTypes : ProofTraceTypes]
  [proofNetworkEntry : ProofTraceTypes.Has Network.ProofEntryT]
  [proofRandomEntry : ProofTraceTypes.Has Random.ProofEntryT]
  [proofDirectCoreEvent : ProofTraceTypes.Has
    (ProtocolEvent.ProofEntryT (CoreEvent Payload))]
  [proofCoreEvent : ProofTraceTypes.Has
    (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage Payload)))]
  [proofRequestResponseEvent : ProofTraceTypes.Has
    (ProtocolEvent.ProofEntryT (RequestResponseEvent Payload))]
  [proofDirectPkeKeys : ProofTraceTypes.Has
    (LongTermKeys.ProofEntryT (pkeKeyName Payload))]
  [proofDirectSignatureKeys : ProofTraceTypes.Has
    (LongTermKeys.ProofEntryT (signatureKeyName Payload))]
  [proofPkeKeys : ProofTraceTypes.Has
    (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage Payload)))]
  [proofSignatureKeys : ProofTraceTypes.Has
    (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage Payload)))]
  [proofCommunicationState : ProofTraceTypes.Has
    (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState Payload))]

attribute [reducible, scoped instance] HasProofTrace.proofTraceTypes
attribute [reducible, scoped instance] HasProofTrace.proofNetworkEntry
attribute [reducible, scoped instance] HasProofTrace.proofRandomEntry
attribute [reducible, scoped instance] HasProofTrace.proofDirectCoreEvent
attribute [reducible, scoped instance] HasProofTrace.proofCoreEvent
attribute [reducible, scoped instance] HasProofTrace.proofRequestResponseEvent
attribute [reducible, scoped instance] HasProofTrace.proofDirectPkeKeys
attribute [reducible, scoped instance] HasProofTrace.proofDirectSignatureKeys
attribute [reducible, scoped instance] HasProofTrace.proofPkeKeys
attribute [reducible, scoped instance] HasProofTrace.proofSignatureKeys
attribute [reducible, scoped instance] HasProofTrace.proofCommunicationState

#combine +toplevel into ProofEntryT from
  Network,
  Random,
  ProtocolEvent (CoreEvent Payload),
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName Payload),
  LongTermKeys (signatureKeyName Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),

public instance : HasProofTrace where

section CryptoPredicates

public instance [BytesWellFormed] : RequestResponseEventPredicates Payload :=
  defaultRequestResponseEventPredicates Payload

public instance : PublicKeyEncryption.EncryptPred :=
  corePkeEncryptPred (WireMessage Payload)

public instance [BytesInvariants]
    [BytesInvariants.Has PublicKeyEncryption.Pk.invariants] :
    PublicKeyEncryption.EncryptPredProof :=
  corePkeEncryptPredProof (WireMessage Payload) rfl

public instance : Signature.SignPred := coreSignPred (WireMessage Payload)

public instance [BytesInvariants] : Signature.SignPredProof :=
  coreSignPredProof (WireMessage Payload) rfl

public instance : AEAD.EncryptPred := requestResponseAEADPredicate (α := Payload)

public instance [BytesInvariants] : AEAD.EncryptPredProof :=
  requestResponseAEADPredicateProof (α := Payload) rfl

end CryptoPredicates

public class HasBytesInvariants extends HasProofTrace where
  [pkePredicate : PublicKeyEncryption.EncryptPred]
  [signaturePredicate : Signature.SignPred]
  [aeadPredicate : AEAD.EncryptPred]
  [bytesInvariants : BytesInvariants]
  [bytesInvariantsProofs : BytesInvariantsProofs]
  [randomInvariant : BytesInvariants.Has Random.invariants]
  [literalInvariant : BytesInvariants.Has Literal.invariants]
  [concatInvariant : BytesInvariants.Has Concat.invariants]
  [pkeInvariant : BytesInvariants.Has PublicKeyEncryption.invariants]
  [signatureInvariant : BytesInvariants.Has Signature.invariants]
  [aeadInvariant : BytesInvariants.Has AEAD.invariants]

attribute [instance_reducible, scoped instance] HasBytesInvariants.pkePredicate
attribute [instance_reducible, scoped instance] HasBytesInvariants.signaturePredicate
attribute [instance_reducible, scoped instance] HasBytesInvariants.aeadPredicate
attribute [reducible, scoped instance] HasBytesInvariants.bytesInvariants
attribute [scoped instance] HasBytesInvariants.bytesInvariantsProofs
attribute [scoped instance] HasBytesInvariants.randomInvariant
attribute [scoped instance] HasBytesInvariants.literalInvariant
attribute [scoped instance] HasBytesInvariants.concatInvariant
attribute [scoped instance] HasBytesInvariants.pkeInvariant
attribute [scoped instance] HasBytesInvariants.signatureInvariant
attribute [scoped instance] HasBytesInvariants.aeadInvariant

section BytesInvariantComposition

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

public instance : HasBytesInvariants where
  pkePredicate := corePkeEncryptPred (WireMessage Payload)
  signaturePredicate := coreSignPred (WireMessage Payload)
  aeadPredicate := requestResponseAEADPredicate (α := Payload)

end BytesInvariantComposition

section InvariantComponents

public abbrev pkeLabel (participant : Participant) (publicKey : Bytes) : Label :=
  LongTermKeys.label (pkeKeyName (WireMessage Payload)) participant publicKey

public abbrev signatureLabel (participant : Participant) (verificationKey : Bytes) : Label :=
  LongTermKeys.label (signatureKeyName (WireMessage Payload)) participant verificationKey

public instance : LongTermKeys.ProofConfig
    (pkeKeyName (WireMessage Payload)) (fun _ => communicationPkeUsage (WireMessage Payload)) pkeLabel := by
  unfold pkeLabel
  exact communicationPkeProofConfig (α := WireMessage Payload)

public def directPkeLabel (participant : Participant) (publicKey : Bytes) : Label :=
  LongTermKeys.label (pkeKeyName Payload) participant publicKey

public def directSignatureLabel
    (participant : Participant) (verificationKey : Bytes) : Label :=
  LongTermKeys.label (signatureKeyName Payload) participant verificationKey

public instance : LongTermKeys.ProofConfig
    (pkeKeyName Payload) (fun _ => communicationPkeUsage Payload) directPkeLabel where
  IsLongTermPublicKey _ publicKey tr := publicKey.Publishable tr
  label_canFlow := by
    intro participant publicKey tr
    unfold directPkeLabel
    exact canFlowRefl _ _
  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

public instance : LongTermKeys.ProofConfig
    (signatureKeyName Payload) (fun _ => communicationSignatureUsage Payload) directSignatureLabel where
  IsLongTermPublicKey _ verificationKey tr := verificationKey.Publishable tr
  label_canFlow := by
    intro participant verificationKey tr
    unfold directSignatureLabel
    exact canFlowRefl _ _
  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

public instance : LongTermKeys.ProofConfig
    (signatureKeyName (WireMessage Payload)) (fun _ => communicationSignatureUsage (WireMessage Payload)) signatureLabel :=
  communicationSignatureProofConfig (α := WireMessage Payload)

public instance : PersistentLocalUpdateableState.CompromisableLocalStateInv
    (CommunicationState Payload) := communicationStateInv (α := Payload)

public instance : ProtocolEvent.EventInv (CoreEvent (WireMessage Payload)) :=
  coreEventInv (α := WireMessage Payload)

public instance : HigherLayerEventPredicates Payload :=
  defaultHigherLayerEventPredicates Payload

public instance : ProtocolEvent.EventInv (CoreEvent Payload) :=
  coreEventInv (α := Payload)

public instance : ProtocolEvent.EventInv (RequestResponseEvent Payload) :=
  requestResponseEventInv (α := Payload)

-- Public request bytes cannot justify impersonating an uncompromised client.
example (tr : ProofTrace) (client server : Participant) (request : Payload) (key : Bytes)
    (honest : ¬ participantCommunicationCompromised (α := WireMessage Payload) client tr.erase)
    (received : requestResponseEventInvariant tr
      (.serverReceiveRequest (some client) server request key : RequestResponseEvent Payload)) :
    tr.erase.EventLogged
      (.clientSendRequest .authenticated client server request key : RequestResponseEvent Payload) := by
  simp only [requestResponseEventInvariant] at received
  exact received.2.2.2.resolve_right (fun h => honest h.1)

end InvariantComponents

public class HasTraceInvariant extends HasBytesInvariants where
  [directCoreEventInvariant : ProtocolEvent.EventInv (CoreEvent Payload)]
  [coreEventInvariant : ProtocolEvent.EventInv (CoreEvent (WireMessage Payload))]
  [requestResponseEventInvariant : ProtocolEvent.EventInv (RequestResponseEvent Payload)]
  [stateInvariant : PersistentLocalUpdateableState.CompromisableLocalStateInv
    (CommunicationState Payload)]
  [traceInvariant : TraceInvariant]
  [traceNetwork : TraceInvariant.Has Network.ProofEntryT]
  [traceRandom : TraceInvariant.Has Random.ProofEntryT]
  [traceDirectCoreEvent : TraceInvariant.Has
    (ProtocolEvent.ProofEntryT (CoreEvent Payload))]
  [traceCoreEvent : TraceInvariant.Has
    (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage Payload)))]
  [traceRequestResponseEvent : TraceInvariant.Has
    (ProtocolEvent.ProofEntryT (RequestResponseEvent Payload))]
  [traceCommunicationState : TraceInvariant.Has
    (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState Payload))]
  [baseAttackerKnowledgeTheorem : BaseAttackerKnowledgeTheorem]
  [attackerKnowledgeTheorem : AttackerKnowledgeTheorem]

attribute [instance_reducible, scoped instance] HasTraceInvariant.directCoreEventInvariant
attribute [instance_reducible, scoped instance] HasTraceInvariant.coreEventInvariant
attribute [instance_reducible, scoped instance] HasTraceInvariant.requestResponseEventInvariant
attribute [instance_reducible, scoped instance] HasTraceInvariant.stateInvariant
attribute [reducible, scoped instance] HasTraceInvariant.traceInvariant
attribute [scoped instance] HasTraceInvariant.traceNetwork
attribute [scoped instance] HasTraceInvariant.traceRandom
attribute [scoped instance] HasTraceInvariant.traceDirectCoreEvent
attribute [scoped instance] HasTraceInvariant.traceCoreEvent
attribute [scoped instance] HasTraceInvariant.traceRequestResponseEvent
attribute [scoped instance] HasTraceInvariant.traceCommunicationState
attribute [scoped instance] HasTraceInvariant.baseAttackerKnowledgeTheorem
attribute [scoped instance] HasTraceInvariant.attackerKnowledgeTheorem

section TraceInvariantComposition

#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  Random,
  ProtocolEvent (CoreEvent Payload),
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName Payload),
  LongTermKeys (signatureKeyName Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

public instance : HasTraceInvariant where
  directCoreEventInvariant := coreEventInv (α := Payload)
  coreEventInvariant := coreEventInv (α := WireMessage Payload)
  requestResponseEventInvariant := requestResponseEventInv (α := Payload)
  stateInvariant := communicationStateInv (α := Payload)

end TraceInvariantComposition

-- The public API exposes IDs while specifications retain the complete request as a proof witness.
example (handles : CommunicationKeyHandles) (client server : Participant) (request : Payload) :
    HoareTriple (sendRequest handles client server request)
      (fun tr => IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := Payload) client server)) request tr)
      (fun result tr => ∃ metadata : CommunicationMetadata Payload,
        CommClientProperties tr.erase client server result.2 metadata ∧ metadata.request = request ∧
        tr.erase.EventLogged (.clientSendRequest .unauthenticated client server request metadata.key : RequestResponseEvent Payload)) := by
  have spec := sendRequest.proof (α := Payload) handles client server request
  apply HoareTriple.mk
  intro tr hrequest hinvariant
  exact spec.pf tr ⟨True.intro, hrequest⟩ hinvariant

example (handles : CommunicationKeyHandles) (client server : Participant) (request : Payload) :
    HoareTriple (sendRequestAuthenticated handles client server request)
      (fun tr => IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := Payload) client server)) request tr)
      (fun result tr => ∃ metadata : CommunicationMetadata Payload,
        CommClientAuthenticatedCondition tr.erase client server result.2 metadata ∧ metadata.request = request ∧
        tr.erase.EventLogged (.clientSendRequest .authenticated client server request metadata.key : RequestResponseEvent Payload)) := by
  have spec := sendRequestAuthenticated.proof (α := Payload) handles client server request
  constructor
  intro tr hrequest htr
  exact spec.pf tr ⟨True.intro, hrequest⟩ htr

example (handles : CommunicationKeyHandles) (server : Participant) (handle : Nat) :
    HoareTriple (receiveRequest (α := Payload) handles server handle)
      (fun _ => True)
      (fun result tr => ∃ metadata : CommunicationMetadata Payload,
        CommServerProperties tr.erase server metadata result.2 ∧ metadata.client = none ∧ metadata.request = result.1) :=
  receiveRequest.proof handles server handle

example (handles : CommunicationKeyHandles) (server : Participant) (handle : Nat) :
    HoareTriple (receiveRequestAuthenticated (α := Payload) handles server handle)
      (fun _ => True)
      (fun result tr => ∃ metadata : CommunicationMetadata Payload,
        (metadata.server = server ∧ metadata.stateHandle = result.2 ∧ PersistentLocalUpdateableState.StateWasSet tr.erase server result.2 (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _)) ∧ metadata.client.isSome = true ∧ metadata.request = result.1 ∧
        tr.erase.EventLogged (.serverReceiveRequest metadata.client server result.1 metadata.key : RequestResponseEvent Payload)) :=
  receiveRequestAuthenticated.proof handles server handle

example (client : Participant) (stateId handle : Nat) :
    HoareTriple (receiveResponse (α := Payload) client stateId handle) (fun _ => True)
      (fun response tr => ∃ metadata : CommunicationMetadata Payload,
        (metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)) ∧ tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent Payload)) :=
  by
  apply HoareTriple.mk
  intro tr hpre htr
  step
  grind

example (client server : Participant) :
    HoareTriple (initializeRequestResponse (α := Payload) client server) (fun _ => True) (fun _ _ => True) :=
  initializeRequestResponse.proof client server

-- Compose the core contracts through `step` with the concrete predicate composition.
example (sending receiving : CommunicationKeyHandles) (sender receiver : Participant)
    (payload : WireMessage Payload) :
    HoareTriple (do
      let handle ← sendConfidential sending sender receiver payload
      receiveConfidential receiving receiver handle)
      (fun tr => HigherLayerEventPredicates.confidential tr sender receiver payload ∧
        IsWellFormed (Bytes.KnowableBy (communicationLabel (α := WireMessage Payload) sender receiver)) payload tr)
      (fun message tr => message.receiver = receiver ∧ tr.erase.EventLogged
        (.confidentialReceive message.sender receiver message.payload : CoreEvent (WireMessage Payload))) := by
  step
  step
  grind

example (sending receiving : CommunicationKeyHandles) (sender receiver : Participant)
    (payload : WireMessage Payload) :
    HoareTriple (do
      let handle ← sendAuthenticated sending sender receiver payload
      receiveAuthenticated receiving receiver handle)
      (fun tr => HigherLayerEventPredicates.authenticated tr sender receiver payload ∧
        IsWellFormed Bytes.Publishable payload tr)
      (fun message tr => message.receiver = receiver ∧ tr.erase.EventLogged
        (.authenticatedReceive message.sender receiver message.payload : CoreEvent (WireMessage Payload))) := by
  step
  step
  grind

example (sending receiving : CommunicationKeyHandles) (sender receiver : Participant)
    (payload : WireMessage Payload) :
    HoareTriple (do
      let handle ← sendConfidentialAuthenticated sending sender receiver payload
      receiveConfidentialAuthenticated receiving receiver handle)
      (fun tr => HigherLayerEventPredicates.confidentialAuthenticated tr sender receiver payload ∧
        IsWellFormed (Bytes.KnowableBy (communicationLabel (α := WireMessage Payload) sender receiver)) payload tr)
      (fun message tr => message.receiver = receiver ∧ tr.erase.EventLogged
        (.confidentialAuthenticatedReceive message.sender receiver message.payload : CoreEvent (WireMessage Payload))) := by
  step
  step
  grind

example (sender receiver : Participant) :
    HoareTriple (initializeCore (α := WireMessage Payload) sender receiver) (fun _ => True) (fun _ _ => True) := by
  step
  grind

example :
    ReachableImpliesInvariant (sendRequest.reachability (α := Payload)) := sendRequest.reachability.sound

example :
    ReachableImpliesInvariant (receiveResponse.reachability (α := Payload)) := inferInstance

example :
    ReachableImpliesInvariant
      (compromiseCommunicationState.reachability (α := Payload)) := inferInstance

-- Reachability preservation must use the concrete operation specifications.
example : ReachableImpliesInvariant (sendRequestAuthenticated.reachability (α := Payload)) :=
  sendRequestAuthenticated.reachability.sound

example : ReachableImpliesInvariant (receiveRequest.reachability (α := Payload)) :=
  receiveRequest.reachability.sound

example : ReachableImpliesInvariant (receiveRequestAuthenticated.reachability (α := Payload)) :=
  receiveRequestAuthenticated.reachability.sound

example : ReachableImpliesInvariant (sendResponse.reachability (α := Payload)) := inferInstance

example : ReachableImpliesInvariant (receiveResponseAuthenticated.reachability (α := Payload)) := inferInstance

example : ReachableImpliesInvariant (initializeRequestResponse.reachability (α := Payload)) := inferInstance

-- Receives and compromise are admitted even with invalid handles; failure must
-- preserve the invariant instead of excluding the call from reachability.
example (handles : CommunicationKeyHandles) (server : Participant) (handle : Nat) (tr : ExecTrace) :
    (receiveRequest.reachability (α := Payload)).PreCond (handles, server, handle) tr := by trivial

example (client : Participant) (metadata : CommunicationMetadata Payload) (handle : Nat) (tr : ExecTrace) :
    (receiveResponse.reachability (α := Payload)).PreCond (client, metadata.stateHandle, handle) tr := by trivial

example (handle : Nat) (tr : ExecTrace) :
    (compromiseCommunicationState.reachability (α := Payload)).PreCond ("Alice", handle) tr := by trivial

-- The default higher-layer policy admits public string requests without any
-- assumption about executing sendRequest or its resulting trace.
example (handles : CommunicationKeyHandles) (client server : Participant) (request : Payload) (tr : ExecTrace) :
    (sendRequest.reachability (α := Payload)).PreCond (handles, client, server, request) tr := by
  intro proofTr _ _
  exact ⟨True.intro, by simp⟩

-- A denied higher-layer request cannot become reachable through the wrapper.
example [preds : RequestResponseEventPredicates Payload] (handles : CommunicationKeyHandles) (client server : Participant) (request : Payload) (tr : ProofTrace)
    (htr : tr.Invariant) (hdenied : ¬ RequestResponseEventPredicates.sendRequest tr client server request (requestResponseLabel (α := Payload) client server)) :
    ¬ (sendRequest.reachability (α := Payload)).PreCond (handles, client, server, request) tr.erase := by
  intro hpre
  exact hdenied (hpre tr rfl htr).1

-- Every core trace action has a reachability preservation proof under the
-- concrete core configuration used by request/response.
example : ReachableImpliesInvariant (sendConfidential.reachability (α := WireMessage Payload)) := inferInstance

example : ReachableImpliesInvariant (receiveConfidential.reachability (α := WireMessage Payload)) := inferInstance

example : ReachableImpliesInvariant (sendAuthenticated.reachability (α := WireMessage Payload)) :=
  sendAuthenticated.reachability.sound

example : ReachableImpliesInvariant (receiveAuthenticated.reachability (α := WireMessage Payload)) :=
  receiveAuthenticated.reachability.sound

example : ReachableImpliesInvariant (sendConfidentialAuthenticated.reachability (α := WireMessage Payload)) :=
  sendConfidentialAuthenticated.reachability.sound

example : ReachableImpliesInvariant (receiveConfidentialAuthenticated.reachability (α := WireMessage Payload)) :=
  receiveConfidentialAuthenticated.reachability.sound

example : ReachableImpliesInvariant (initializeCore.reachability (α := WireMessage Payload)) := inferInstance

-- Invalid receive handles remain admissible; their failure must preserve the invariant.
example (handles : CommunicationKeyHandles) (receiver : Participant) (handle : Nat) (tr : ExecTrace) :
    (receiveConfidentialAuthenticated.reachability (α := WireMessage Payload)).PreCond (handles, receiver, handle) tr := by trivial

-- Request/response disables plain authenticated sends in its core policy.
-- Public payloads alone must not bypass that policy in the reachability config.
example (handles : CommunicationKeyHandles) (sender receiver : Participant) (payload : WireMessage Payload) (tr : ProofTrace) (htr : tr.Invariant) :
    ¬ (sendAuthenticated.reachability (α := WireMessage Payload)).PreCond (handles, sender, receiver, payload) tr.erase := by
  intro hpre
  exact (hpre tr rfl htr).1

end ProofComposition

end DY.Communication.Test
