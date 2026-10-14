module

public import DyLibraries.SplitCrypto.SplitAEAD

public import DyLibraries.Communication.RequestResponse.Invariants
public import DyLibraries.Communication.Core.Lemmas
public import DY.Trace.ReachabilityTheorem
import all DyLibraries.Communication.RequestResponse
import all DyLibraries.Communication.Data
import all DyLibraries.Communication.RequestResponse.Invariants
import all DyLibraries.Communication.Core
import all DyLibraries.Communication.Core.Invariants
import all DyExtensions.Actions.ProtocolEvent
import all DyExtensions.Actions.PersistentLocalUpdateableState
import DY.Meta.Step
import all DY.Trace.Manipulation
import all DY.Trace.Monad
import all DyExtensions.Comparse

namespace DY.Communication

open DY.Comparse

section PureSpecifications

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has AEAD.SubF]
variable [ParseableSerializeable α] [DecidableEq α]
variable [ExecTraceTypes] [ProofTraceTypes]

public instance (metadata : CommunicationMetadata α) :
    HoareTriplePure (requestAuthentication metadata)
      (fun _ => True)
      (fun result _ => result = requestAuthentication metadata) where
  pf := by simp

end PureSpecifications

section ExecutionProperties

set_option linter.unusedSectionVars false

section EventProperties

variable [BytesFunctor] [ExecTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]

/-- Appending a protocol event records it independently of any proof invariant. -/
private theorem eventLogged_append
  (tr : ExecTrace) (event : RequestResponseEvent α) :
  (tr.append (ProtocolEvent.ExecEntryT.mk event)).EventLogged event
:= by
  exact ⟨tr.length, Trace.at?_append tr (ProtocolEvent.ExecEntryT.mk event)⟩

/-- Logging an event appends its execution entry and succeeds. -/
private theorem logEvent_run
  (tr : ExecTrace) (event : RequestResponseEvent α) :
  (ProtocolEvent.logEvent event).run tr = (some (), ⟨tr.append (ProtocolEvent.ExecEntryT.mk event), Trace.append_le _ _⟩)
:= by
  rfl

end EventProperties

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has AEAD.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [DecidableEq α] [RequestResponseConfig α]
variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent (WireMessage α)))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

/-- Successful sending logs the original request, independently of trace invariants. -/
public theorem sendRequest.properties
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  ∀ tr : ExecTrace,
    let (result, trOut) := (sendRequest handles client server request).run tr
    ∀ messageHandle stateId, result = some (messageHandle, stateId) →
      ∃ key, trOut.val.EventLogged (.clientSendRequest .unauthenticated client server request key : RequestResponseEvent α)
:= by
  intro tr
  simp only [sendRequest, Traceful.run_bind, logEvent_run]
  split <;> simp_all
  rename_i key hkey
  have hlogged := eventLogged_append ((Random.genRand 32).run tr).2.val (.clientSendRequest .unauthenticated client server request key : RequestResponseEvent α)
  split <;> simp_all
  dsimp only [Traceful.run, ProtocolEvent.logEvent, appendEntry, Traceful.mk, Bind.bind, Pure.pure] at *
  split <;> simp_all
  grind only [Trace.EventLogged_le, Trace.le_trans, Subtype.property]

/-- Successful authenticated sending logs the original client and request. -/
public theorem sendRequestAuthenticated.properties
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  ∀ tr : ExecTrace,
    let (result, trOut) := (sendRequestAuthenticated handles client server request).run tr
    ∀ messageHandle stateId, result = some (messageHandle, stateId) →
      ∃ key, trOut.val.EventLogged (.clientSendRequest .authenticated client server request key : RequestResponseEvent α)
:= by
  intro tr
  simp only [sendRequestAuthenticated, Traceful.run_bind, logEvent_run]
  split <;> simp_all
  rename_i key hkey
  have hlogged := eventLogged_append ((Random.genRand 32).run tr).2.val (.clientSendRequest .authenticated client server request key : RequestResponseEvent α)
  split <;> simp_all
  dsimp only [Traceful.run, ProtocolEvent.logEvent, appendEntry, Traceful.mk, Bind.bind, Pure.pure] at *
  split <;> simp_all
  grind only [Trace.EventLogged_le, Trace.le_trans, Subtype.property]

/-- Successful anonymous reception logs the returned payload. -/
public theorem receiveRequest.properties
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  ∀ tr : ExecTrace,
    let (result, trOut) := (receiveRequest (α := α) handles server messageHandle).run tr
    ∀ request stateId, result = some (request, stateId) →
      ∃ key, trOut.val.EventLogged (.serverReceiveRequest none server request key : RequestResponseEvent α)
:= by
  intro tr
  simp only [receiveRequest, Traceful.run_bind]
  split <;> simp_all
  split <;> simp_all [Traceful.run_bind, Traceful.run_pure, Traceful.run_failure]
  rename_i message hmessage hwire request hrequest
  have hlogged := eventLogged_append ((receiveConfidential (α := WireMessage α) handles server messageHandle).run tr).2.val (.serverReceiveRequest none server request.request request.key : RequestResponseEvent α)
  split <;> simp_all
  dsimp only [Traceful.run, ProtocolEvent.logEvent, appendEntry, Traceful.mk, Bind.bind, Pure.pure] at *
  grind only [Trace.EventLogged_le, Subtype.property]

/-- Successful authenticated reception logs the sender and returned payload. -/
public theorem receiveRequestAuthenticated.properties
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  ∀ tr : ExecTrace,
    let (result, trOut) := (receiveRequestAuthenticated (α := α) handles server messageHandle).run tr
    ∀ request stateId, result = some (request, stateId) →
      ∃ client key, trOut.val.EventLogged (.serverReceiveRequest (some client) server request key : RequestResponseEvent α)
:= by
  intro tr
  simp only [receiveRequestAuthenticated, Traceful.run_bind]
  split <;> simp_all
  split <;> simp_all [Traceful.run_bind, Traceful.run_pure, Traceful.run_failure]
  rename_i message hmessage hwire request hrequest
  have hlogged := eventLogged_append ((receiveConfidentialAuthenticated (α := WireMessage α) handles server messageHandle).run tr).2.val (.serverReceiveRequest (some message.sender) server request.request request.key : RequestResponseEvent α)
  split <;> simp_all
  dsimp only [Traceful.run, ProtocolEvent.logEvent, appendEntry, Traceful.mk, Bind.bind, Pure.pure] at *
  grind only [Trace.EventLogged_le, Subtype.property]

end ExecutionProperties

section TracefulSpecifications

set_option linter.unusedSectionVars false

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has AEAD.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [DecidableEq α] [RequestResponseConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent (WireMessage α)))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

section StateSpecifications
variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
attribute [local instance] communicationStateInv
variable [ProofTraceTypes.Has (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]

/-- A fresh communication address retains its initial value as a historical write. -/
@[instance]
private theorem storeCommunicationState.proof
  (participant : Participant) (state : CommunicationState α) :
  HoareTriple (storeCommunicationState participant state)
    (fun tr => requestResponseStateInvariant participant state tr)
    (fun stateId tr => PersistentLocalUpdateableState.StateWasSet tr.erase participant stateId state)
:= by
  unfold storeCommunicationState
  step
  rename_i hfresh
  mark_non_monotone hfresh
  step by
    simp_all [PersistentLocalUpdateableState.LocalStateInv.invariant,
      PersistentLocalUpdateableState.IsMostRecentStateFor]
  rename_i hwrite hrecent
  clear hrecent
  step
  grind [PersistentLocalUpdateableState.StateWasSet]

/-- Loading request metadata establishes a persistent witness for its state ID. -/
@[instance]
private theorem getClientMetadata.proof
  (client : Participant) (stateId : Nat) :
  HoareTriple (getClientMetadata (α := α) client stateId)
    (fun _ => True)
    (fun metadata tr =>
      metadata.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _))
:= by
  apply HoareTriple.mk
  intro tr _ htr
  unfold getClientMetadata
  step
  rename_i state hrecent hinv
  have hw : PersistentLocalUpdateableState.StateWasSet tr.erase client stateId state := by
    obtain ⟨time, hw, _⟩ := PersistentLocalUpdateableState.isMostRecentStateFor_spec client stateId state tr.erase hrecent
    exact ⟨time, hw⟩
  clear hrecent
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  step
  simp_all

/-- Loading request metadata establishes a persistent witness for its state ID. -/
@[instance]
private theorem getServerMetadata.proof
  (server : Participant) (stateId : Nat) :
  HoareTriple (getServerMetadata (α := α) server stateId)
    (fun _ => True)
    (fun metadata tr =>
      metadata.server = server ∧
      metadata.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase server stateId (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _))
:= by
  apply HoareTriple.mk
  intro tr _ htr
  unfold getServerMetadata
  step
  rename_i state hrecent hinv
  have hw : PersistentLocalUpdateableState.StateWasSet tr.erase server stateId state := by
    obtain ⟨time, hw, _⟩ := PersistentLocalUpdateableState.isMostRecentStateFor_spec server stateId state tr.erase hrecent
    exact ⟨time, hw⟩
  clear hrecent
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  step
  simp_all

/-- Equality-only updates make every historical value at a communication address identical. -/
public theorem communicationState_unique
  (tr : ProofTrace) (participant : Participant) (stateId : Nat) (left right : CommunicationState α) :
  tr.Invariant →
    PersistentLocalUpdateableState.StateWasSet tr.erase participant stateId left →
    PersistentLocalUpdateableState.StateWasSet tr.erase participant stateId right → left = right
:= by
  rintro hinv ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
  have horder : t₁ < t₂ ∨ t₁ = t₂ ∨ t₂ < t₁ := by omega
  rcases horder with hlt | heq | hgt
  · exact PersistentLocalUpdateableState.stateWasSetTwice_implies_updatePred tr t₁ t₂ participant stateId left right hinv h₁ h₂ hlt
  · subst t₂
    unfold PersistentLocalUpdateableState.StateWasSetAt at h₁ h₂
    grind
  · exact (PersistentLocalUpdateableState.stateWasSetTwice_implies_updatePred tr t₂ t₁ participant stateId right left hinv h₂ h₁ hgt).symm

/-- A client state ID determines a unique metadata witness. -/
public theorem clientMetadata_unique
  (tr : ProofTrace) (client : Participant) (stateId : Nat) (left right : CommunicationMetadata α) :
  tr.Invariant →
    (left.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨left.client, left.server, left.request, left.key⟩ : CommunicationState _)) →
    (right.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨right.client, right.server, right.request, right.key⟩ : CommunicationState _)) →
    left = right
:= by
  intro hinv hl hr
  have heq := communicationState_unique tr client stateId _ _ hinv hl.2 hr.2
  cases left
  cases right
  simp_all

/-- A server state ID determines a unique metadata witness. -/
public theorem serverMetadata_unique
  (tr : ProofTrace) (server : Participant) (stateId : Nat) (left right : CommunicationMetadata α) :
  tr.Invariant →
    (left.server = server ∧
      left.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase server stateId (.serverReceiveRequest ⟨left.client, left.request, left.key⟩ : CommunicationState _)) →
    (right.server = server ∧
      right.stateHandle = stateId ∧
      PersistentLocalUpdateableState.StateWasSet tr.erase server stateId (.serverReceiveRequest ⟨right.client, right.request, right.key⟩ : CommunicationState _)) →
    left = right
:= by
  intro hinv hl hr
  have heq := communicationState_unique tr server stateId _ _ hinv hl.2.2 hr.2.2
  cases left
  cases right
  simp_all

end StateSpecifications

private theorem requestResponseLabel_canFlow_coreLabel
    (client server : Participant) (tr : ExecTrace) :
    (requestResponseLabel (α := α) client server).canFlow
      (communicationLabel (α := WireMessage α) client server) tr := by
  simp only [Label.canFlow, requestResponseLabel, Label.joinIsCorrupt,
    requestResponseParticipantLabel_isCorrupt, communicationLabel]
  grind [participantCommunicationCompromised]

private theorem decodeResponseMessage_parts
    (server : Participant) (key messageBytes : Bytes) (metadata : CommunicationMetadata α)
    (response : α)
    (h : decodeResponseMessage server key messageBytes metadata = some response) :
    ∃ envelope : ResponseEnvelope, ∃ plaintext : Bytes,
      parse (a := WireMessage α) messageBytes = some (.response envelope) ∧
      AEAD.decrypt key envelope.nonce envelope.ciphertext
        (serialize ({client := metadata.client, server} : AssociatedData)) = some plaintext ∧
      parse plaintext = some response := by
  simp only [decodeResponseMessage, bind, pure, instMonadErr._aux_13, instMonadErr._aux_5, OptionT.bind, OptionT.pure, OptionT.mk, OptionT.fail, failure, instAlternativeErr._aux_1] at h
  repeat' (split at h <;> simp_all)
  all_goals grind

section SendRequest

-- Request keys must be fresh at the prefix where their send event is logged.
attribute [local instance 1100] Random.genRand.fresh_spec

variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
-- PKE predicates are not indexed by the payload type, so specialize the
-- concrete instance inside the assumption that consumes it.
variable [PublicKeyEncryption.EncryptPred] [PublicKeyEncryption.EncryptPredProof]
variable [PublicKeyEncryption.EncryptPred.Has (pkeKeyName (WireMessage α)) (corePkeEncryptPred (WireMessage α))]
variable [BytesInvariants.Has PublicKeyEncryption.Ciphertext.invariants]
variable [RequestResponseEventPredicates α]

-- Fix the event and state predicates before elaborating `TraceInvariant.Has`,
-- so its instances certify these concrete communication-layer invariants.
attribute [local instance] coreEventInv requestResponseEventInv communicationStateInv

variable [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has Random.invariants]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage α)))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage α)))]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [ProofTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]

-- Local label and format rules let `step` discharge the request envelope's
-- precondition, following the invariant automation used by SignedDH.
attribute [local grind] requestResponseLabel
attribute [local grind =] WireMessage.IsWellFormed_eq RequestMessage.IsWellFormed_eq

public def CommClientProperties
  (tr : ExecTrace) (client server : Participant) (stateId : Nat) (metadata : CommunicationMetadata α) :
  Prop
:=
  metadata.stateHandle = stateId ∧
  metadata.server = server ∧
  metadata.client = none ∧
  PersistentLocalUpdateableState.StateWasSet tr client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)

/-- The returned state ID retains the request and its logged communication event. -/
@[instance]
public theorem sendRequest.proof
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  HoareTriple (sendRequest handles client server request)
    (fun tr =>
      RequestResponseEventPredicates.sendRequest tr client server request (requestResponseLabel (α := α) client server) ∧
      IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client server)) request tr)
    (fun result tr => ∃ metadata : CommunicationMetadata α,
      CommClientProperties tr.erase client server result.2 metadata ∧
      metadata.request = request ∧
      tr.erase.EventLogged (.clientSendRequest .unauthenticated client server request metadata.key : RequestResponseEvent α))
:= by
  apply HoareTriple.mk
  unfold sendRequest
  -- Generate the shared AEAD response key with its label and key usage.
  step with ⟨fun _ => requestResponseLabel (α := α) client server, requestResponseKeyUsage (α := α)⟩
  rename_i key hfresh
  mark_non_monotone hfresh
  step by
    simp only [ProtocolEvent.EventInv.invariant, requestResponseEventInvariant, requestResponseEventFreshness]
    grind
  step by
    simp only [requestResponseStateInvariant]
    grind
  rename_i stateId hstored
  step by
    simp only [HigherLayerEventPredicates.confidential]
    have hflow := requestResponseLabel_canFlow_coreLabel (α := α) client server tr.erase
    grind [IsWellFormed_KnowableBy_canFlow]
  step
  refine ⟨{ key, client := none, server, stateHandle := stateId, request }, ?_⟩
  grind [CommClientProperties]

private theorem receiveConfidentialRequest_spec
    (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
    HoareTriple (receiveConfidential (α := WireMessage α) handles server messageHandle)
      (fun _ => True)
      (fun message tr => message.receiver = server ∧
        ∀ req, message.payload = .request req →
          requestResponseEventInvariant tr (.serverReceiveRequest none server req.request req.key)) := by
  apply HoareTriple.mk
  step
  rename_i hreceiver hevent
  refine ⟨hreceiver, ?_⟩
  intro req hreq
  obtain ⟨i, hi⟩ := Trace.EventLogged_imp_EventInv _ tr h hevent
  have hsource : tr.erase.EventLogged
      (.confidentialSend x.sender x.receiver x.payload : CoreEvent (WireMessage α)) ∨
      IsWellFormed Bytes.Publishable x.payload tr := by
    have hinv := coreEventInvariant_later _ (tr.prefix i) tr (by grind) hi
    simpa only [coreEventInvariant, hreceiver] using hinv
  rw [← hreceiver]
  rcases hsource with hs | hpub
  · obtain ⟨i, hi⟩ := Trace.EventLogged_imp_EventInv _ tr h hs
    have hrr : (tr.prefix i).erase.EventLogged
        (.clientSendRequest .unauthenticated x.sender x.receiver req.request req.key : RequestResponseEvent α) := by
      simpa only [ProtocolEvent.EventInv.invariant, coreEventInvariant, requestResponseCoreHigherLayerPredicates,
        HigherLayerEventPredicates.confidential, hreq] using hi.2
    have hrr' : tr.erase.EventLogged
        (.clientSendRequest .unauthenticated x.sender x.receiver req.request req.key : RequestResponseEvent α) := by grind
    have hf := requestResponseEventInvariant_of_logged _ tr h hrr'
    simp only [requestResponseEventInvariant] at hf ⊢
    grind
  · simp only [hreq, WireMessage.IsWellFormed_eq, RequestMessage.IsWellFormed_eq] at hpub
    simp only [requestResponseEventInvariant]
    have hk : req.key.KnowableBy (requestResponseParticipantLabel (α := α) x.receiver) tr :=
      ⟨hpub.1.1, canFlowTrans _ _ _ _ hpub.1.2 (Label.pubCanFlow _ _)⟩
    have hr : IsWellFormed (Bytes.KnowableBy (req.key.label tr)) req.request tr := by
      rw [← KnowableBy_serialize]
      have hs : (serialize req.request).Publishable tr := by simpa only [Publishable_serialize] using hpub.2
      exact ⟨hs.1, canFlowTrans _ _ _ _ hs.2 (Label.pubCanFlow _ _)⟩
    grind [Bytes.HasUsage_public]

attribute [local instance 1100] receiveConfidentialRequest_spec

/-- Received request metadata identifies its retained state and logged reception event. -/
@[expose] public def CommServerProperties
  (tr : ExecTrace) (server : Participant) (metadata : CommunicationMetadata α) (stateId : Nat) :
  Prop
:=
  metadata.stateHandle = stateId ∧
  metadata.server = server ∧
  PersistentLocalUpdateableState.StateWasSet tr server stateId (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _) ∧
  tr.EventLogged (.serverReceiveRequest metadata.client server metadata.request metadata.key : RequestResponseEvent α)

/-- A received request's historical state and reception event persist as the trace grows. -/
public theorem CommServerProperties.later
  (server : Participant) (metadata : CommunicationMetadata α) (stateId : Nat) (a b : ExecTrace) :
  a ≤ b →
    CommServerProperties a server metadata stateId →
    CommServerProperties b server metadata stateId
:= by
  grind [CommServerProperties, PersistentLocalUpdateableState.stateWasSet_later]

grind_pattern [grind_later] CommServerProperties.later => a ≤ b, CommServerProperties a server metadata stateId


/-- The returned state ID retains the request and its logged communication event. -/
@[instance]
public theorem receiveRequest.proof
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  HoareTriple (receiveRequest handles server messageHandle)
    (fun _ => True)
    (fun result tr => ∃ metadata : CommunicationMetadata α,
      CommServerProperties tr.erase server metadata result.2 ∧
      metadata.client = none ∧ metadata.request = result.1)
:= by
  apply HoareTriple.mk
  intro tr _ htr
  unfold receiveRequest
  step
  rename_i message hreceiver hmessage
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_bind, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  rename_i requestMessage hrequest
  step
  step by
    simp only [ProtocolEvent.EventInv.invariant, requestResponseEventFreshness]
    grind
  step by
    simp_all only [requestResponseStateInvariant,
      requestResponseEventInvariant]
    try simp_all only [AuthenticatedMetadata.toMetadata]
    grind
  rename_i stateId hstored
  step
  refine ⟨{ key := requestMessage.key, client := none, server, stateHandle := stateId, request := requestMessage.request }, ?_⟩
  grind [CommServerProperties]

section AuthenticatedSend

variable [Signature.SignPred]
variable [Signature.SignPred.Has (signatureKeyName (WireMessage α)) (coreSignPred (WireMessage α))]
variable [BytesInvariants.Has Signature.invariants]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]

public def CommClientAuthenticatedCondition
  (tr : ExecTrace) (client server : Participant) (stateId : Nat) (metadata : CommunicationMetadata α) :
  Prop
:=
  metadata.stateHandle = stateId ∧
  metadata.server = server ∧
  metadata.client = some client ∧
  PersistentLocalUpdateableState.StateWasSet tr client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)


/-- The returned state ID retains the request and its logged communication event. -/
@[instance]
public theorem sendRequestAuthenticated.proof
  (handles : CommunicationKeyHandles) (client server : Participant) (request : α) :
  HoareTriple (sendRequestAuthenticated handles client server request)
    (fun tr =>
      RequestResponseEventPredicates.sendRequest tr client server request (requestResponseLabel (α := α) client server) ∧
      IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client server)) request tr)
    (fun result tr => ∃ metadata : CommunicationMetadata α,
      CommClientAuthenticatedCondition tr.erase client server result.2 metadata ∧
      metadata.request = request ∧
      tr.erase.EventLogged (.clientSendRequest .authenticated client server request metadata.key : RequestResponseEvent α))
:= by
  apply HoareTriple.mk
  unfold sendRequestAuthenticated
  -- Generate the shared AEAD response key with its label and key usage.
  step with ⟨fun _ => requestResponseLabel (α := α) client server, requestResponseKeyUsage (α := α)⟩
  rename_i key hfresh
  mark_non_monotone hfresh
  step by
    simp only [ProtocolEvent.EventInv.invariant, requestResponseEventInvariant, requestResponseEventFreshness]
    grind
  step by
    simp only [requestResponseStateInvariant]
    grind
  rename_i stateId hstored
  step by
    simp only [HigherLayerEventPredicates.confidentialAuthenticated]
    have hflow := requestResponseLabel_canFlow_coreLabel (α := α) client server tr.erase
    grind [IsWellFormed_KnowableBy_canFlow]
  step
  refine ⟨{ key, client := some client, server, stateHandle := stateId, request }, ?_⟩
  grind [CommClientAuthenticatedCondition]

/-- A confidential authenticated core reception establishes the request/response receive invariant. -/
private theorem receiveConfidentialAuthenticatedRequest_spec
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  HoareTriple (receiveConfidentialAuthenticated (α := WireMessage α) handles server messageHandle)
    (fun _ => True)
    (fun message tr => message.receiver = server ∧
      ∀ req, message.payload = .request req → requestResponseEventInvariant tr
        (.serverReceiveRequest (some message.sender) server req.request req.key)) := by
  apply HoareTriple.mk
  step
  rename_i hreceiver hevent
  refine ⟨hreceiver, ?_⟩
  intro req hreq
  obtain ⟨i, hi⟩ := Trace.EventLogged_imp_EventInv _ tr h hevent
  have hinv := coreEventInvariant_later _ (tr.prefix i) tr (by grind) hi
  obtain ⟨hauth, hconf⟩ := hinv
  have fromEvent : tr.erase.EventLogged
      (.confidentialAuthenticatedSend x.sender server x.payload : CoreEvent (WireMessage α)) →
      tr.erase.EventLogged (.clientSendRequest .authenticated x.sender server req.request req.key : RequestResponseEvent α) := by
    intro he
    obtain ⟨i, hi⟩ := Trace.EventLogged_imp_EventInv _ tr h he
    have hr : (tr.prefix i).erase.EventLogged
        (.clientSendRequest .authenticated x.sender server req.request req.key : RequestResponseEvent α) := by
      simpa only [ProtocolEvent.EventInv.invariant, coreEventInvariant, requestResponseCoreHigherLayerPredicates,
        HigherLayerEventPredicates.confidentialAuthenticated, hreq] using hi.2
    grind
  by_cases he : tr.erase.EventLogged
      (.confidentialAuthenticatedSend x.sender server x.payload : CoreEvent (WireMessage α))
  · have hr := fromEvent he
    have hf := requestResponseEventInvariant_of_logged _ tr h hr
    simp only [requestResponseEventInvariant] at hf ⊢
    grind
  · have hpub : req.key.Publishable tr ∧ IsWellFormed Bytes.Publishable req.request tr := by
      have hp : IsWellFormed Bytes.Publishable x.payload tr := hconf.resolve_left he
      simpa only [hreq, WireMessage.IsWellFormed_eq, RequestMessage.IsWellFormed_eq] using hp
    have hk : req.key.KnowableBy (requestResponseParticipantLabel (α := α) server) tr :=
      ⟨hpub.1.1, canFlowTrans _ _ _ _ hpub.1.2 (Label.pubCanFlow _ _)⟩
    have hr : IsWellFormed (Bytes.KnowableBy (req.key.label tr)) req.request tr := by
      rw [← KnowableBy_serialize]
      have hs : (serialize req.request).Publishable tr := by simpa only [Publishable_serialize] using hpub.2
      exact ⟨hs.1, canFlowTrans _ _ _ _ hs.2 (Label.pubCanFlow _ _)⟩
    simp only [requestResponseEventInvariant]
    grind [Bytes.HasUsage_public]

attribute [local instance 1100] receiveConfidentialAuthenticatedRequest_spec

/-- The returned state ID retains the request and its logged communication event. -/
@[instance]
public theorem receiveRequestAuthenticated.proof
  (handles : CommunicationKeyHandles) (server : Participant) (messageHandle : Nat) :
  HoareTriple (receiveRequestAuthenticated handles server messageHandle)
    (fun _ => True)
    (fun result tr => ∃ metadata : CommunicationMetadata α,
      (metadata.server = server ∧ metadata.stateHandle = result.2 ∧ PersistentLocalUpdateableState.StateWasSet tr.erase server result.2 (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _)) ∧
      metadata.client.isSome = true ∧ metadata.request = result.1 ∧
      tr.erase.EventLogged (.serverReceiveRequest metadata.client server result.1 metadata.key : RequestResponseEvent α))
:= by
  apply HoareTriple.mk
  intro tr _ htr
  unfold receiveRequestAuthenticated
  step
  rename_i message hreceiver hmessage
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_bind, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  rename_i requestMessage hrequest
  step
  step by
    simp only [ProtocolEvent.EventInv.invariant, requestResponseEventFreshness]
    grind
  step by
    simp_all only [requestResponseStateInvariant,
      requestResponseEventInvariant]
    try simp_all only [AuthenticatedMetadata.toMetadata]
    grind
  rename_i stateId hstored
  step
  refine ⟨{ key := requestMessage.key, client := some message.sender, server, stateHandle := stateId, request := requestMessage.request }, ?_⟩
  grind

end AuthenticatedSend

end SendRequest

section RemainingSpecifications

attribute [local grind_later .] Bytes.WellFormed.later Bytes.label_later

variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable [RequestResponseEventPredicates α]
attribute [local instance] requestResponseEventInv communicationStateInv
variable [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has Random.invariants]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [ProofTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]

private theorem response_event_matches_request
    (client : Participant) (metadata : CommunicationMetadata α) (response : α)
    (tr : ProofTrace) (htr : tr.Invariant)
    (_hkey : metadata.key.Invariant tr)
    (hlabel : metadata.key.label tr = requestResponseLabel (α := α) client metadata.server)
    (hsent : tr.erase.EventLogged
      (.clientSendRequest (requestAuthentication metadata) client metadata.server metadata.request metadata.key :
        RequestResponseEvent α))
    (hevent : ∃ request, tr.erase.EventLogged
      (.serverSendResponse metadata.client metadata.server request response metadata.key : RequestResponseEvent α)) :
    tr.erase.EventLogged (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key :
      RequestResponseEvent α) ∨
    (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
    (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase := by
  obtain ⟨request, hevent⟩ := hevent
  have hs := requestResponseEventInvariant_of_logged _ tr htr hevent
  simp only [requestResponseEventInvariant] at hs
  have hr := requestResponseEventInvariant_of_logged _ tr htr hs.1
  simp only [requestResponseEventInvariant] at hr
  have hu : ∀ auth cl srv req, tr.erase.EventLogged
      (.clientSendRequest auth cl srv req metadata.key : RequestResponseEvent α) → req = metadata.request := by
    intro auth cl srv req h
    exact (clientSendRequest_unique tr htr auth (requestAuthentication metadata) cl client srv metadata.server
      req metadata.request metadata.key h hsent).2.2.2
  have hpub : metadata.key.Publishable tr →
      (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
      (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase := by
    simp only [Bytes.Publishable, hlabel, ← canFlowPubEqIsCorrupt, requestResponseLabel, Label.joinIsCorrupt]
    grind
  cases hc : metadata.client <;> simp only [hc] at hr hevent ⊢ <;> grind

section Responses

variable [AEAD.EncryptPred] [AEAD.EncryptPredProof]
variable [AEAD.EncryptPred.Has (aeadKeyName α) (requestResponseAEADPredicate (α := α))]
variable [BytesInvariants.Has AEAD.Ciphertext.invariants]

private theorem decodeResponseMessage.proof
    (client server : Participant) (key messageBytes : Bytes) (metadata : CommunicationMetadata α) :
    HoareTriple (decodeResponseMessage server key messageBytes metadata)
      (fun tr => server = metadata.server ∧ key = metadata.key ∧
        metadata.key.Invariant tr ∧
        metadata.key.label tr = requestResponseLabel (α := α) client metadata.server ∧
        tr.erase.EventLogged (.clientSendRequest (requestAuthentication metadata) client metadata.server
          metadata.request metadata.key : RequestResponseEvent α) ∧
        (metadata.client = none ∨ metadata.client = some client) ∧ messageBytes.Publishable tr)
      (fun response tr => requestResponseEventInvariant tr (.clientReceiveResponse client response metadata)) := by
  constructor
  intro tr hpre htr
  obtain ⟨rfl, rfl, hk, hl, hsent, hc, hmsg⟩ := hpre
  change (match decodeResponseMessage metadata.server metadata.key messageBytes metadata with
    | none => True
    | some response => requestResponseEventInvariant tr (.clientReceiveResponse client response metadata))
  split
  · trivial
  · rename_i response hdec
    obtain ⟨envelope, plaintext, hwire, hdecrypt, hparse⟩ :=
      decodeResponseMessage_parts _ _ _ _ _ hdec
    have henv : envelope.nonce.Publishable tr ∧ envelope.ciphertext.Publishable tr := by
      have hwf : IsWellFormed Bytes.Publishable (.response envelope : WireMessage α) tr := by grind
      simpa only [WireMessage.IsWellFormed_eq, ResponseEnvelope.IsWellFormed_eq] using hwf
    have had : (serialize ({client := metadata.client, server := metadata.server} : AssociatedData)).Publishable tr := by simp
    have hout := AEAD.decrypt.Invariant _ _ _ _ _ tr hk henv.1.1 henv.2.1 had.1 hdecrypt
    have heq : serialize response = plaintext := (serialize_parse_inv _ _ hparse).symm
    subst plaintext
    have hknow : IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) response tr := by
      rw [← KnowableBy_serialize]
      rcases hout.2 with hp | hp
      · exact ⟨hout.1, AEAD.EncryptPredProof.pred_key_label _ _ _ _ _ _ hp⟩
      · exact ⟨hp.2.1, canFlowTrans _ _ _ _ hp.2.2 (Label.pubCanFlow _ _)⟩
    have hauth : tr.erase.EventLogged
        (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key : RequestResponseEvent α) ∨
        (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
        (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase := by
      rcases hout.2 with hp | hp
      · have hrequest := requestResponseEventInvariant_of_logged _ tr htr hsent
        have hu : metadata.key.HasUsage (requestResponseKeyUsage (α := α)) tr := hrequest.2.2.2.1
        rcases hu with hu | hpub
        · rw [hu] at hp
          have hlocal := (AEAD.EncryptPred.HasStep.pred_eq (tag := aeadKeyName α) (component := requestResponseAEADPredicate (α := α)) _ _ _ _ _ tr rfl rfl).mp hp
          simp only [AEAD.EncryptPred.pred, parse_serialize_inv] at hlocal
          exact response_event_matches_request client metadata response tr htr hk hl hsent hlocal.1
        · simp only [hl, ← canFlowPubEqIsCorrupt, requestResponseLabel, Label.joinIsCorrupt] at hpub
          exact Or.inr hpub
      · have hpub := hp.1.2
        simp only [hl, ← canFlowPubEqIsCorrupt, requestResponseLabel, Label.joinIsCorrupt] at hpub
        exact Or.inr hpub
    simp only [requestResponseEventInvariant]
    exact ⟨hl ▸ hknow, hk, hl, hsent, hauth, hc⟩

@[instance]
private theorem computeResponseMessage.proof
    (server : Participant) (metadata : CommunicationMetadata α) (nonce : Bytes) (response : α) :
    HoareTriplePure (computeResponseMessage server metadata nonce response)
      (fun tr =>
        metadata.key.KnowableBy (requestResponseParticipantLabel (α := α) server) tr ∧
        metadata.key.HasUsage (requestResponseKeyUsage (α := α)) tr ∧
        IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) response tr ∧
        nonce.Publishable tr ∧
        tr.erase.EventLogged (.serverSendResponse metadata.client server metadata.request response
          metadata.key : RequestResponseEvent α))
      (fun message tr => message.Publishable tr) := by
  constructor
  intro tr hpre
  have hm : (serialize response).KnowableBy (metadata.key.label tr) tr := by
    simpa only [KnowableBy_serialize] using hpre.2.2.1
  have had : (serialize ({ client := metadata.client, server } : AssociatedData)).Publishable tr := by
    simp
  have hp : AEAD.EncryptPred.pred (metadata.key.usage tr) metadata.key nonce (serialize response) (serialize ({ client := metadata.client, server } : AssociatedData)) tr ∨
      metadata.key.Publishable tr ∧ (serialize response).Publishable tr := by
    rcases hpre.2.1 with hu | hpub
    · left
      rw [hu]
      apply (AEAD.EncryptPred.HasStep.pred_eq (tag := aeadKeyName α) (component := requestResponseAEADPredicate (α := α)) _ _ _ _ _ tr rfl rfl).mpr
      simp only [AEAD.EncryptPred.pred, parse_serialize_inv]
      exact ⟨⟨metadata.request, hpre.2.2.2.2⟩, hm.2⟩
    · exact Or.inr ⟨⟨hpre.1.1, hpub⟩, ⟨hm.1, canFlowTrans _ _ _ _ hm.2 hpub⟩⟩
  unfold computeResponseMessage
  simp only [Publishable_serialize, WireMessage.IsWellFormed_eq, ResponseEnvelope.IsWellFormed_eq]
  grind [AEAD.encrypt.Invariant, AEAD.encrypt.label]

@[instance]
private theorem sendResponseWithMetadata.proof
    (server : Participant) (metadata : CommunicationMetadata α) (response : α) :
    HoareTriple (sendResponseWithMetadata server metadata response)
      (fun tr =>
        tr.erase.EventLogged (.serverReceiveRequest metadata.client server metadata.request metadata.key :
          RequestResponseEvent α) ∧
        RequestResponseEventPredicates.sendResponse tr metadata.client server metadata.request response
          (metadata.key.label tr) ∧
        IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) response tr)
      (fun _ tr => tr.erase.EventLogged
        (.serverSendResponse metadata.client server metadata.request response metadata.key :
          RequestResponseEvent α)) := by
  apply HoareTriple.mk
  intro tr hpre htr
  have hreceived := requestResponseEventInvariant_of_logged _ tr htr hpre.1
  simp only [requestResponseEventInvariant] at hreceived
  have hkey := hreceived.1.1
  have hrequest := IsWellFormed_KnowableBy_implies_WellFormed _ _ _ hreceived.2.1
  have hresponse := IsWellFormed_KnowableBy_implies_WellFormed _ _ _ hpre.2.2
  have hpre' := hpre
  clear hpre hreceived
  unfold sendResponseWithMetadata
  step
  rename_i hrecent hstate
  clear hrecent
  split <;> try dsimp only
  all_goals try solve | simp [wp, Traceful.run_bind, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
  step
  step
  step
  step
  step
  step by
    simp_all only [PersistentLocalUpdateableState.LocalStateInv.invariant, requestResponseStateInvariant,
      ProtocolEvent.EventInv.invariant, requestResponseEventInvariant, requestResponseEventFreshness]
    grind [IsWellFormed_KnowableBy_implies_WellFormed]
  step with ⟨fun _ => Label.pub, Usage.nothing⟩
  hoist
  step by
    simp_all only [PersistentLocalUpdateableState.LocalStateInv.invariant, requestResponseStateInvariant]
    grind
  step
  grind

@[instance]
private theorem receiveResponseWithMetadata.proof
    (client : Participant) (metadata : CommunicationMetadata α) (messageHandle : Nat) :
    HoareTriple (receiveResponseWithMetadata client metadata messageHandle)
      (fun _ => True)
      (fun response tr => tr.erase.EventLogged
        (.clientReceiveResponse client response metadata : RequestResponseEvent α)) := by
  letI (server : Participant) (key message : Bytes) :=
    decodeResponseMessage.proof client server key message metadata
  apply HoareTriple.mk
  intro tr _ htr
  unfold receiveResponseWithMetadata
  step
  rename_i hrecent hstate
  clear hrecent
  split <;> try dsimp only
  all_goals
    split <;> try dsimp only
    all_goals try solve | simp [wp, Traceful.run_bind, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩
    repeat' (step by
      simp_all only [PersistentLocalUpdateableState.LocalStateInv.invariant, requestResponseStateInvariant,
        requestAuthentication, ProtocolEvent.EventInv.invariant,
        requestResponseEventFreshness, requestResponseEventInvariant]
      try grind)
    all_goals grind

@[instance]
private theorem receiveResponseAuthenticatedWithMetadata.proof
    (client : Participant) (metadata : AuthenticatedMetadata α) (messageHandle : Nat) :
    HoareTriple (receiveResponseAuthenticatedWithMetadata client metadata messageHandle)
      (fun _ => True)
      (fun response tr => tr.erase.EventLogged
        (.clientReceiveResponse client response metadata.toMetadata : RequestResponseEvent α)) := by
  unfold receiveResponseAuthenticatedWithMetadata
  step
  grind

/-- Sending a response reads its metadata from the retained server state and logs the response
for that request, provided the response is authorized and knowable under the stored key label. -/
@[instance]
public theorem sendResponse.proof
  (server : Participant) (stateId : Nat) (response : α) :
  HoareTriple (sendResponse server stateId response)
    (fun tr => ∃ metadata : CommunicationMetadata α,
      CommServerProperties tr.erase server metadata stateId ∧
      RequestResponseEventPredicates.sendResponse tr metadata.client server metadata.request response (metadata.key.label tr) ∧
      IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) response tr)
    (fun _ tr => ∀ metadata : CommunicationMetadata α,
      (metadata.server = server ∧ metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet tr.erase server stateId (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _)) →
      tr.erase.EventLogged (.serverSendResponse metadata.client server metadata.request response metadata.key : RequestResponseEvent α))
:= by
  apply HoareTriple.mk
  intro tr hpre htr
  obtain ⟨expected, hpre⟩ := hpre
  simp only [CommServerProperties] at hpre
  have hreceived := requestResponseEventInvariant_of_logged _ tr htr hpre.1.2.2.2
  simp only [requestResponseEventInvariant] at hreceived
  have hkey : expected.key.Invariant tr := hreceived.1.1
  have hrequest := IsWellFormed_KnowableBy_implies_WellFormed _ _ _ hreceived.2.1
  have hresponse := IsWellFormed_KnowableBy_implies_WellFormed _ _ _ hpre.2.2
  have hpre' := hpre
  clear hpre hreceived
  unfold sendResponse
  step
  expose_names
  have heq : metadata = expected := by grind [serverMetadata_unique]
  subst metadata
  step
  grind [serverMetadata_unique]

/-- Successful response reception identifies the retained request and logs its response. -/
@[instance]
public theorem receiveResponse.proof
  (client : Participant) (stateId messageHandle : Nat) :
  HoareTriple (receiveResponse (α := α) client stateId messageHandle)
    (fun _ => True)
    (fun response tr => ∃ metadata : CommunicationMetadata α,
      -- TODO is this postcondition even needed?
      (metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)) ∧
      tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α))
:= by
  apply HoareTriple.mk
  unfold receiveResponse
  step
  step
  grind

/-- Authenticated response reception additionally checks the retained client identity. -/
@[instance]
public theorem receiveResponseAuthenticated.proof
  (client : Participant) (stateId messageHandle : Nat) :
  HoareTriple (receiveResponseAuthenticated (α := α) client stateId messageHandle)
    (fun _ => True)
    (fun response tr => ∃ metadata : CommunicationMetadata α,
      (metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)) ∧ metadata.client = some client ∧
      tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α))
:= by
  unfold receiveResponseAuthenticated
  step
  step
  step
  grind

end Responses


/-- Exposing a participant's communication state preserves the invariant, including on failure. -/
@[instance]
public theorem compromiseCommunicationState.proof
  (participant : Participant) (stateId : Nat) :
  HoareTriple (compromiseCommunicationState (α := α) participant stateId)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromiseCommunicationState
  step
  grind

section Initialization

variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
variable [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]

@[instance]
public theorem initializeRequestResponse.proof (client server : Participant) :
    HoareTriple (initializeRequestResponse (α := α) client server)
      (fun _ => True) (fun _ _ => True) := by
  unfold initializeRequestResponse initializeCore
  step
  split
  step
  split
  step
  split
  step
  split
  step
  grind

end Initialization

end RemainingSpecifications
end TracefulSpecifications
section Reachability

variable [ExecTraceTypes]

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has AEAD.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [DecidableEq α] [RequestResponseConfig α]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent (WireMessage α)))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

@[expose] public def receiveRequest.reachability : ReachabilityConfig :=
  .make (fun (handles, server, messageHandle) => receiveRequest (α := α) handles server messageHandle)

@[expose] public def receiveRequestAuthenticated.reachability : ReachabilityConfig :=
  .make (fun (handles, server, messageHandle) => receiveRequestAuthenticated (α := α) handles server messageHandle)

@[expose] public def receiveResponse.reachability : ReachabilityConfig :=
  .make (fun (client, metadata, messageHandle) => receiveResponse (α := α) client metadata messageHandle)

@[expose] public def receiveResponseAuthenticated.reachability : ReachabilityConfig :=
  .make (fun (client, metadata, messageHandle) => receiveResponseAuthenticated (α := α) client metadata messageHandle)

@[expose] public def initializeRequestResponse.reachability : ReachabilityConfig :=
  .make (fun (client, server) => initializeRequestResponse (α := α) client server)

@[expose] public def compromiseCommunicationState.reachability : ReachabilityConfig :=
  .make (fun (participant, stateHandle) => compromiseCommunicationState (α := α) participant stateHandle)

section SendConfigurations

variable [ProofTraceTypes] [TraceInvariant] [BytesInvariants] [RequestResponseEventPredicates α]

/-- Sending is authorized by the higher-layer predicate and payload knowability.
These proof-trace predicates are required on invariant lifts of the execution
trace; the precondition makes no assumption about the action's outcome. -/
@[expose] public def sendRequest.reachability : ReachabilityConfig where
  Input := CommunicationKeyHandles × Participant × Participant × α
  PreCond := fun (_, client, server, request) tr => ∀ proofTr : ProofTrace, proofTr.erase = tr → proofTr.Invariant →
    RequestResponseEventPredicates.sendRequest proofTr client server request (requestResponseLabel (α := α) client server) ∧
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client server)) request proofTr
  step := fun (handles, client, server, request) => ⟨_, sendRequest handles client server request⟩

/-- Authenticated requests have the same caller obligations as anonymous requests. -/
@[expose] public def sendRequestAuthenticated.reachability : ReachabilityConfig where
  Input := CommunicationKeyHandles × Participant × Participant × α
  PreCond := (sendRequest.reachability (α := α)).PreCond
  step := fun (handles, client, server, request) => ⟨_, sendRequestAuthenticated handles client server request⟩

/-- Responses require a matching received request, higher-layer authorization,
and a payload knowable under the response-key label. -/
@[expose] public def sendResponse.reachability : ReachabilityConfig where
  Input := Participant × Nat × α
  PreCond := fun (server, stateId, response) tr => ∀ proofTr : ProofTrace, proofTr.erase = tr → proofTr.Invariant →
    ∃ metadata : CommunicationMetadata α, (metadata.server = server ∧ metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet proofTr.erase server stateId (.serverReceiveRequest ⟨metadata.client, metadata.request, metadata.key⟩ : CommunicationState _)) ∧
    proofTr.erase.EventLogged (.serverReceiveRequest metadata.client server metadata.request metadata.key : RequestResponseEvent α) ∧
    RequestResponseEventPredicates.sendResponse proofTr metadata.client server metadata.request response (metadata.key.label proofTr) ∧
    IsWellFormed (Bytes.KnowableBy (metadata.key.label proofTr)) response proofTr
  step := fun (server, metadata, response) => ⟨_, sendResponse server metadata response⟩

end SendConfigurations

section Proofs

set_option linter.unusedSectionVars false

variable [ProofTraceTypes] [TraceInvariant]

section SendRequest

variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
-- PKE predicates are not indexed by the payload type, so specialize the
-- concrete instance inside the assumption that consumes it.
variable [PublicKeyEncryption.EncryptPred] [PublicKeyEncryption.EncryptPredProof]
variable [PublicKeyEncryption.EncryptPred.Has (pkeKeyName (WireMessage α)) (corePkeEncryptPred (WireMessage α))]
variable [BytesInvariants.Has PublicKeyEncryption.Ciphertext.invariants]
variable [RequestResponseEventPredicates α]

-- Fix the event and state predicates before elaborating `TraceInvariant.Has`,
-- so its instances certify these concrete communication-layer invariants.
attribute [local instance] coreEventInv requestResponseEventInv communicationStateInv

variable [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has Random.invariants]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage α)))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (CoreEvent (WireMessage α)))]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [ProofTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem sendRequest.reachability.sound : ReachableImpliesInvariant (sendRequest.reachability (α := α)) where
  pf := by
    rintro ⟨handles, client, server, request⟩
    change HoareTriple (sendRequest (α := α) handles client server request) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    have hcaller := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step
    trivial

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem receiveRequest.reachability.sound : ReachableImpliesInvariant (receiveRequest.reachability (α := α)) where
  pf := by
    rintro ⟨handles, server, messageHandle⟩
    change HoareTriple (receiveRequest (α := α) handles server messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

section AuthenticatedSend

variable [Signature.SignPred]
variable [Signature.SignPred.Has (signatureKeyName (WireMessage α)) (coreSignPred (WireMessage α))]
variable [BytesInvariants.Has Signature.invariants]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem sendRequestAuthenticated.reachability.sound
  : ReachableImpliesInvariant (sendRequestAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, client, server, request⟩
    change HoareTriple (sendRequestAuthenticated (α := α) handles client server request) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    have hcaller := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step
    trivial

/-- The unchanged reachability action preserves the invariant under the registered channel policies. -/
public theorem receiveRequestAuthenticated.reachability.sound
  : ReachableImpliesInvariant (receiveRequestAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨handles, server, messageHandle⟩
    change HoareTriple (receiveRequestAuthenticated (α := α) handles server messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

end AuthenticatedSend

end SendRequest

section RemainingSpecifications

attribute [local grind_later .] Bytes.WellFormed.later Bytes.label_later

variable [BytesInvariants] [BytesInvariantsProofs]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable [RequestResponseEventPredicates α]
attribute [local instance] requestResponseEventInv communicationStateInv
variable [ProofTraceTypes.Has Network.ProofEntryT] [TraceInvariant.Has Network.ProofEntryT]
variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has Random.invariants]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [ProofTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has
  (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]

section Responses

variable [AEAD.EncryptPred] [AEAD.EncryptPredProof]
variable [AEAD.EncryptPred.Has (aeadKeyName α) (requestResponseAEADPredicate (α := α))]
variable [BytesInvariants.Has AEAD.Ciphertext.invariants]

public instance : ReachableImpliesInvariant (sendResponse.reachability (α := α)) where
  pf := by
    rintro ⟨server, metadata, response⟩
    change HoareTriple (sendResponse (α := α) server metadata response) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    obtain ⟨witness, hcaller⟩ := hpre tr rfl htr
    mark_non_monotone hcaller
    clear hpre
    step by
      refine ⟨witness, ?_⟩
      grind [CommServerProperties]
    trivial

public instance : ReachableImpliesInvariant (receiveResponse.reachability (α := α)) where
  pf := by
    rintro ⟨client, metadata, messageHandle⟩
    change HoareTriple (receiveResponse (α := α) client metadata messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

public instance : ReachableImpliesInvariant (receiveResponseAuthenticated.reachability (α := α)) where
  pf := by
    rintro ⟨client, metadata, messageHandle⟩
    change HoareTriple (receiveResponseAuthenticated (α := α) client metadata messageHandle) _ _
    apply HoareTriple.mk
    intro tr hpre htr
    clear hpre
    step
    trivial

end Responses


public instance : ReachableImpliesInvariant (compromiseCommunicationState.reachability (α := α)) where
  pf input := compromiseCommunicationState.proof input.1 input.2

section Initialization

variable [BytesInvariants.Has PublicKeyEncryption.Pk.invariants]
variable [Signature.SignPred] [BytesInvariants.Has Signature.invariants]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [ProofTraceTypes.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (pkeKeyName (WireMessage α)))]
variable [TraceInvariant.Has (LongTermKeys.ProofEntryT (signatureKeyName (WireMessage α)))]

public instance : ReachableImpliesInvariant (initializeRequestResponse.reachability (α := α)) where
  pf := fun (client, server) => initializeRequestResponse.proof client server

end Initialization

end RemainingSpecifications
end Proofs
end Reachability

end DY.Communication
