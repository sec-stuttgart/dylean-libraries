module

public import DY.Communication.RequestResponse
public import DY.Communication.Core.Invariants

namespace DY.Communication

open DY.Comparse

public def communicationStateCompromised
    [BytesFunctor] [ExecTraceTypes]
    [ExecTraceTypes.Has
      (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
    (participant : Participant) (tr : ExecTrace) : Prop :=
  ∃ stateId, ∃ state : CommunicationState α,
    PersistentLocalUpdateableState.LocalStateCompromised participant stateId state tr

public theorem communicationStateCompromised_later
    [BytesFunctor] [ExecTraceTypes]
    [ExecTraceTypes.Has
      (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
    (participant : Participant) (tr1 tr2 : ExecTrace) :
    tr1 ≤ tr2 → communicationStateCompromised (α := α) participant tr1 →
    communicationStateCompromised (α := α) participant tr2 := by
  simp [communicationStateCompromised]
  grind

grind_pattern communicationStateCompromised_later =>
  tr1 ≤ tr2, communicationStateCompromised (α := α) participant tr1

/-- Request/response participant labels account only for the communication
keys and communication-state entries in scope for this layer. -/
public def requestResponseParticipantLabel
    [BytesFunctor] [ExecTraceTypes] [RequestResponseConfig α]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [ExecTraceTypes.Has
      (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
    [ExecTraceTypes.Has
      (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
    [ExecTraceTypes.Has
      (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
    (participant : Participant) : Label where
  isCorrupt tr :=
    participantCommunicationCompromised (α := WireMessage α) participant tr ∨
    communicationStateCompromised (α := α) participant tr

@[simp]
public theorem requestResponseParticipantLabel_isCorrupt
    [BytesFunctor] [ExecTraceTypes] [RequestResponseConfig α]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [ExecTraceTypes.Has
      (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
    [ExecTraceTypes.Has
      (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
    [ExecTraceTypes.Has
      (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
    (participant : Participant) (tr : ExecTrace) :
    (requestResponseParticipantLabel (α := α) participant).isCorrupt tr =
      (participantCommunicationCompromised (α := WireMessage α) participant tr ∨
        communicationStateCompromised (α := α) participant tr) := by
  rfl

section HigherLayerHooks

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [ParseableSerializeable α]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]

@[instance_reducible]
public instance requestResponseCoreHigherLayerPredicates :
    HigherLayerEventPredicates (WireMessage α) where
  confidential tr sender receiver payload :=
    match payload with
    | .request request =>
      tr.erase.EventLogged
        (.clientSendRequest .unauthenticated sender receiver request.request request.key :
          RequestResponseEvent α)
    | _ => False
  authenticated _ _ _ _ := False
  confidentialAuthenticated tr sender receiver payload :=
    match payload with
    | .request request =>
      tr.erase.EventLogged
        (.clientSendRequest .authenticated sender receiver request.request request.key :
          RequestResponseEvent α)
    | _ => False
  confidential_later := by
    intro tr1 tr2 sender receiver payload hle h
    cases payload <;> try contradiction
    exact Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) h
  authenticated_later := by simp
  confidentialAuthenticated_later := by
    intro tr1 tr2 sender receiver payload hle h
    cases payload <;> try contradiction
    exact Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) h

end HigherLayerHooks

section AEADPredicate

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has AEAD.SubF]
variable [ParseableSerializeable α]
variable [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]

@[instance_reducible]
public def requestResponseAEADPredicate
    [DecidableEq α] : AEAD.EncryptPred where
  pred _usage key _nonce message associatedData tr :=
    (match parse (a := α) message, parse (a := AssociatedData) associatedData with
      | some response, some identities =>
        ∃ request,
          tr.erase.EventLogged
            (.serverSendResponse identities.client identities.server request response key :
              RequestResponseEvent α)
      | _, _ => False) ∧
    (message.label tr).canFlow (key.label tr) tr.erase

public theorem requestResponseAEADPredicateProof
    [DecidableEq α]
    [BytesInvariants]
    [pred : AEAD.EncryptPred]
    (hpred : pred = requestResponseAEADPredicate (α := α)) : AEAD.EncryptPredProof := by
  subst pred
  letI : AEAD.EncryptPred := requestResponseAEADPredicate (α := α)
  refine { pred_later := ?_, pred_key_label := ?_ }
  · intro _ _ _ usage key nonce message associatedData tr1 tr2 hk hn hm had hle h
    rcases h with ⟨hevent, hflow⟩
    constructor
    · generalize hmParse : parse (a := α) message = parsedMessage at hevent ⊢
      generalize hadParse : parse (a := AssociatedData) associatedData = parsedAD at hevent ⊢
      cases parsedMessage <;> cases parsedAD <;> try contradiction
      rcases hevent with ⟨request, hevent⟩
      exact ⟨request, Trace.EventLogged_le _ _ _ (Trace.erase_le _ _ hle) hevent⟩
    · have hmLabel := Bytes.label_later message tr1 tr2 hle hm
      have hkLabel := Bytes.label_later key tr1 tr2 hle hk
      rw [← hmLabel, ← hkLabel]
      exact Label.canFlowLater _ _ _ _ (Trace.erase_le _ _ hle) hflow
  · intro usage key nonce message associatedData tr h
    exact h.2

end AEADPredicate

private theorem participantLabel_canFlow_stateLabel
    [BytesFunctor] [ExecTraceTypes] [RequestResponseConfig α]
    [BytesFunctor.Has PublicKeyEncryption.SubF]
    [BytesFunctor.Has Signature.SubF]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
    [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
    [ExecTraceTypes.Has
      (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
    (participant : Participant) (stateId : Nat) (state : CommunicationState α) (tr : ExecTrace) :
    (requestResponseParticipantLabel (α := α) participant).canFlow
      (PersistentLocalUpdateableState.label participant stateId state) tr := by
  intro later hle hcorrupt
  rw [PersistentLocalUpdateableState.label_isCorrupt] at hcorrupt
  exact Or.inr ⟨stateId, state, hcorrupt⟩

section StateInvariant

variable [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes]
variable [BytesInvariants] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [ParseableSerializeable α]

private theorem knowable_serialize (label : Label) (payload : α) (tr : ProofTrace) :
    IsWellFormed (Bytes.KnowableBy label) payload tr =
      (serialize payload).KnowableBy label tr := by
  exact (IsWellFormed_FormatRel _ _ _ _ (serialize_FormatRel payload)).symm

variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [RequestResponseConfig α]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

/-- The request/response key protects both endpoints, including their stored
communication states. -/
public def requestResponseLabel (client server : Participant) : Label :=
  (requestResponseParticipantLabel (α := α) client).join
    (requestResponseParticipantLabel (α := α) server)

/-- DYStar's `AeadKey (comm_layer_aead_tag a) empty`. -/
public def requestResponseKeyUsage : Usage where
  type := "AeadKey"
  tag := aeadKeyName α
  data := some (Literal.literalToBytes .empty)

/-- The communication layer's fixed state predicate, following DYStar's three
state cases.  Key secrecy means the byte invariant and exact label equality.
The client option determines authentication in Lean, so no separate consistency
clause for a stored authentication field is needed. -/
public def requestResponseStateInvariant
    (participant : Participant) (state : CommunicationState α) (tr : ProofTrace) : Prop :=
  match state with
  | .clientSendRequest state =>
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) participant state.server))
      state.request tr ∧
    state.key.Invariant tr ∧
    state.key.label tr = requestResponseLabel (α := α) participant state.server ∧
    state.key.HasUsage (requestResponseKeyUsage (α := α)) tr ∧
    tr.erase.EventLogged
      (.clientSendRequest
        (if state.client.isSome then .authenticated else .unauthenticated)
        participant state.server state.request state.key : RequestResponseEvent α)
  | .serverReceiveRequest state =>
    state.key.KnowableBy (requestResponseParticipantLabel (α := α) participant) tr ∧
    IsWellFormed (Bytes.KnowableBy (state.key.label tr)) state.request tr ∧
    state.key.HasUsage (requestResponseKeyUsage (α := α)) tr
  | .clientReceiveResponse state =>
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) participant state.server))
      state.response tr ∧
    state.key.Invariant tr ∧
    state.key.label tr = requestResponseLabel (α := α) participant state.server

public theorem requestResponseStateInvariant_later
    [BytesInvariantsProofs]
    (participant : Participant) (state : CommunicationState α) (tr1 tr2 : ProofTrace)
    (hle : tr1 ≤ tr2) (h : requestResponseStateInvariant participant state tr1) :
    requestResponseStateInvariant participant state tr2 := by
  cases state <;>
    simp only [requestResponseStateInvariant, knowable_serialize, Bytes.KnowableBy] at h ⊢
  all_goals grind

grind_pattern [grind_later] requestResponseStateInvariant_later =>
  tr1 ≤ tr2, requestResponseStateInvariant participant state tr1

public theorem requestResponseStateInvariant_implies_knowable
    [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
    (participant : Participant) (stateId : Nat) (state : CommunicationState α) (tr : ProofTrace)
    (h : requestResponseStateInvariant participant state tr) :
    IsWellFormed (Bytes.KnowableBy (PersistentLocalUpdateableState.label participant stateId state)) state tr := by
  have hflow := participantLabel_canFlow_stateLabel participant stateId state tr.erase
  cases state <;>
    simp only [requestResponseStateInvariant, CommunicationState.IsWellFormed_eq,
      ClientSendRequest.IsWellFormed_eq, ServerReceiveRequest.IsWellFormed_eq,
      ClientReceiveResponse.IsWellFormed_eq] at h ⊢
  all_goals
    simp only [knowable_serialize, Bytes.KnowableBy] at h ⊢
    grind [requestResponseLabel, canFlowTrans]

@[instance_reducible]
public def communicationStateInv
    [BytesInvariantsProofs]
    [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants] :
    PersistentLocalUpdateableState.CompromisableLocalStateInv (CommunicationState α) where
  invariant participant _ state tr := requestResponseStateInvariant participant state tr
  invariant_later participant _ state := requestResponseStateInvariant_later participant state
  updatePred _ _ old new _ := old = new
  updatePred_later _ _ _ _ _ _ _ h := h
  updatePred_trans _ _ _ _ _ _ h₁ h₂ := h₁.trans h₂
  invariant_implies_KnowableBy := requestResponseStateInvariant_implies_knowable

end StateInvariant

/-- Higher-layer request/response facts supplied by the protocol, corresponding
to DYStar's `comm_reqres_preds`. The communication state invariant stays fixed. -/
public class RequestResponseEventPredicates (α : Type)
    [BytesFunctor] [BytesLength] [ExecTraceTypes] [ProofTraceTypes] [BytesWellFormed]
    [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
    [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
    [ParseableSerializeable α] where
  sendRequest : ProofTrace → Participant → Participant → α → Label → Prop
  sendResponse : ProofTrace → Option Participant → Participant → α → α → Label → Prop
  sendRequest_later : ∀ tr1 tr2 client server request label,
    tr1 ≤ tr2 → IsWellFormed Bytes.WellFormed request tr1 →
    sendRequest tr1 client server request label →
    sendRequest tr2 client server request label
  sendResponse_later : ∀ tr1 tr2 client server request response label,
    tr1 ≤ tr2 → IsWellFormed Bytes.WellFormed request tr1 →
    IsWellFormed Bytes.WellFormed response tr1 →
    sendResponse tr1 client server request response label →
    sendResponse tr2 client server request response label

@[expose, instance_reducible]
public def defaultRequestResponseEventPredicates (α : Type)
    [BytesFunctor] [BytesLength] [ExecTraceTypes] [ProofTraceTypes] [BytesWellFormed]
    [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
    [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
    [ParseableSerializeable α] : RequestResponseEventPredicates α where
  sendRequest _ _ _ _ _ := True
  sendResponse _ _ _ _ _ _ := True
  sendRequest_later := by simp
  sendResponse_later := by simp

grind_pattern [grind_later] RequestResponseEventPredicates.sendRequest_later =>
  tr1 ≤ tr2, RequestResponseEventPredicates.sendRequest tr1 client server request label

grind_pattern [grind_later] RequestResponseEventPredicates.sendResponse_later =>
  tr1 ≤ tr2, RequestResponseEventPredicates.sendResponse tr1 client server request response label

section EventInvariant

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [ParseableSerializeable α] [RequestResponseConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
variable [RequestResponseEventPredicates α]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has
  (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has
  (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]

@[expose]
public def requestResponseEventInvariant
    (tr : ProofTrace) (event : RequestResponseEvent α) : Prop :=
  match event with
  | .clientSendRequest _ client server request key =>
    IsWellFormed
      (Bytes.KnowableBy
        ((requestResponseParticipantLabel (α := α) client).join
          (requestResponseParticipantLabel (α := α) server))) request tr ∧
    key.Invariant tr ∧
    key.label tr = requestResponseLabel (α := α) client server ∧
    key.HasUsage (requestResponseKeyUsage (α := α)) tr ∧
    RequestResponseEventPredicates.sendRequest tr client server request (key.label tr)
  | .serverReceiveRequest client server request key =>
    key.KnowableBy (requestResponseParticipantLabel (α := α) server) tr ∧
    IsWellFormed (Bytes.KnowableBy (key.label tr)) request tr ∧
    key.HasUsage (requestResponseKeyUsage (α := α)) tr ∧
    (match client with
    | none =>
      (∃ client', tr.erase.EventLogged
        (.clientSendRequest .unauthenticated client' server request key :
          RequestResponseEvent α)) ∨
      (key.Publishable tr ∧ IsWellFormed Bytes.Publishable request tr)
    | some client' =>
      tr.erase.EventLogged
        (.clientSendRequest .authenticated client' server request key :
          RequestResponseEvent α) ∨
      (participantCommunicationCompromised (α := WireMessage α) client' tr.erase ∧
        key.Publishable tr ∧ IsWellFormed Bytes.Publishable request tr))
  | .serverSendResponse client server request response key =>
    tr.erase.EventLogged
      (.serverReceiveRequest client server request key : RequestResponseEvent α) ∧
    IsWellFormed Bytes.WellFormed request tr ∧
    IsWellFormed Bytes.WellFormed response tr ∧
    key.Invariant tr ∧
    RequestResponseEventPredicates.sendResponse tr client server request response (key.label tr)
  | .clientReceiveResponse client response metadata =>
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client metadata.server)) response tr ∧
    metadata.key.Invariant tr ∧
    metadata.key.label tr = requestResponseLabel (α := α) client metadata.server ∧
    tr.erase.EventLogged
      (.clientSendRequest (requestAuthentication metadata) client metadata.server
        metadata.request metadata.key : RequestResponseEvent α) ∧
    (tr.erase.EventLogged
        (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key :
          RequestResponseEvent α) ∨
      (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
      (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase) ∧
    (metadata.client = none ∨ metadata.client = some client)

public theorem requestResponseEventInvariant_later [BytesInvariantsProofs]
    (event : RequestResponseEvent α) (tr1 tr2 : ProofTrace)
    (hle : tr1 ≤ tr2) (h : requestResponseEventInvariant tr1 event) :
    requestResponseEventInvariant tr2 event := by
  cases event <;>
    simp only [requestResponseEventInvariant, knowable_serialize, ← WellFormed_serialize, ← Publishable_serialize,
      Bytes.KnowableBy, Bytes.Publishable] at h ⊢
  all_goals grind [RequestResponseEventPredicates.sendRequest_later,
    RequestResponseEventPredicates.sendResponse_later]

grind_pattern [grind_later] requestResponseEventInvariant_later =>
  tr1 ≤ tr2, requestResponseEventInvariant tr1 event

/-- A client send consumes a freshly generated response key. This fact is checked
at the event's own prefix; the remaining event facts persist on later traces. -/
public def requestResponseEventFreshness [BytesFunctor.Has Random.SubF]
    (tr : ProofTrace) (event : RequestResponseEvent α) : Prop :=
  match event with
  | .clientSendRequest _ _ _ _ key => Random.JustGenerated key tr
  | _ => True

variable [BytesFunctor.Has Random.SubF]

@[instance_reducible]
public def requestResponseEventInv :
    ProtocolEvent.EventInv (RequestResponseEvent α) where
  invariant tr event := requestResponseEventInvariant tr event ∧ requestResponseEventFreshness tr event

public theorem requestResponseEventInvariant_of_logged
    [BytesInvariantsProofs] [TraceInvariant]
    [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
    [
      letI : ProtocolEvent.EventInv (RequestResponseEvent α) := requestResponseEventInv (α := α)
      TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
    (event : RequestResponseEvent α) (tr : ProofTrace) (htr : tr.Invariant)
    (hevent : tr.erase.EventLogged event) : requestResponseEventInvariant tr event := by
  letI : ProtocolEvent.EventInv (RequestResponseEvent α) := requestResponseEventInv (α := α)
  obtain ⟨i, h⟩ := Trace.EventLogged_imp_EventInv event tr htr hevent
  exact requestResponseEventInvariant_later event _ tr (by grind) h.1

/-- A fresh response key identifies its unique client-send event. -/
public theorem clientSendRequest_unique
    [BytesInvariantsProofs] [TraceInvariant]
    [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
    [
      letI : ProtocolEvent.EventInv (RequestResponseEvent α) := requestResponseEventInv (α := α)
      TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
    (tr : ProofTrace) (htr : tr.Invariant)
    (auth₁ auth₂ : SenderAuthentication) (client₁ client₂ server₁ server₂ : Participant)
    (request₁ request₂ : α) (key : Bytes)
    (h₁ : tr.erase.EventLogged (.clientSendRequest auth₁ client₁ server₁ request₁ key : RequestResponseEvent α))
    (h₂ : tr.erase.EventLogged (.clientSendRequest auth₂ client₂ server₂ request₂ key : RequestResponseEvent α)) :
    auth₁ = auth₂ ∧ client₁ = client₂ ∧ server₁ = server₂ ∧ request₁ = request₂ := by
  letI : ProtocolEvent.EventInv (RequestResponseEvent α) := requestResponseEventInv (α := α)
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  have hiInv := Trace.EventLoggedAt_imp_EventInv _ i tr htr hi
  have hjInv := Trace.EventLoggedAt_imp_EventInv _ j tr htr hj
  have hiFresh : Random.JustGenerated key (tr.prefix i) := hiInv.2
  have hjFresh : Random.JustGenerated key (tr.prefix j) := hjInv.2
  have heq := hiFresh.trace_length_eq hjFresh
  have hij : i = j := by grind
  subst j
  rw [Trace.EventLoggedAt_eq_getEventAt] at hi hj
  grind

end EventInvariant

end DY.Communication
