module

public import DY.Communication.RequestResponse.Lemmas
import all DY.Communication.RequestResponse.Invariants
import all DY.Communication.RequestResponse
import all DY.Communication.Data
import all DY.Comparse
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Trace.Manipulation
import all DY.Trace.Monad

namespace DY.Communication

open DY.Comparse

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF] [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [RequestResponseConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (RequestResponseEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName (WireMessage α)))]
variable [ExecTraceTypes.Has (PersistentLocalUpdateableState.CompromisableState.ExecEntryT (CommunicationState α))]
variable [RequestResponseEventPredicates α] [TraceInvariant]
attribute [local instance] requestResponseEventInv
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]

/-- Response labels are written directly as `metadata.key.label tr` in this port. -/
public def CommMetaDataKnowable (tr : ProofTrace) (participant : Participant) (metadata : CommunicationMetadata α) : Prop :=
  metadata.key.KnowableBy (requestResponseParticipantLabel (α := α) participant) tr ∧
  IsWellFormed (Bytes.KnowableBy (requestResponseParticipantLabel (α := α) participant)) metadata.request tr

omit [BytesInvariantsProofs] in
public theorem serverAuthentication (tr : ProofTrace) (i : Nat) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLoggedAt (.clientReceiveResponse client response metadata : RequestResponseEvent α) i) :
    (∃ request, (tr.prefix i).erase.EventLogged (.serverSendResponse metadata.client metadata.server request response metadata.key : RequestResponseEvent α)) ∨
    (requestResponseParticipantLabel (α := α) client).isCorrupt (tr.prefix i).erase ∨
    (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt (tr.prefix i).erase := by
  have h := (Trace.EventLoggedAt_imp_EventInv _ i tr htr hevent).1.2.2.2.2.1
  exact h.imp (fun hs => ⟨metadata.request, hs⟩) id

public theorem sendRequestEventProperties (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (metadata : CommunicationMetadata α)
    (hevent : ∃ auth, tr.erase.EventLogged (.clientSendRequest auth client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) metadata.request tr ∧
    requestResponseLabel (α := α) client metadata.server = metadata.key.label tr ∧
    metadata.key.HasUsage (requestResponseKeyUsage (α := α)) tr ∧
    RequestResponseEventPredicates.sendRequest tr client metadata.server metadata.request (metadata.key.label tr) := by
  obtain ⟨auth, hevent⟩ := hevent
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  change IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client metadata.server)) metadata.request tr ∧ _ at h
  exact ⟨h.2.2.1 ▸ h.1, h.2.2.1.symm, h.2.2.2⟩

public theorem deriveCommMetaDataKnowableClient (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (client : Participant)
    (hevent : ∃ auth, tr.erase.EventLogged (.clientSendRequest auth client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    CommMetaDataKnowable tr client metadata := by
  obtain ⟨auth, hevent⟩ := hevent
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  simp only [requestResponseEventInvariant, ← KnowableBy_serialize, Bytes.KnowableBy, requestResponseLabel] at h
  simp only [CommMetaDataKnowable, ← KnowableBy_serialize, Bytes.KnowableBy]
  grind [canFlowTrans]

public theorem deriveCommMetaDataKnowableServer (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (server : Participant)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client server metadata.request metadata.key : RequestResponseEvent α)) :
    CommMetaDataKnowable tr server metadata := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  simp only [requestResponseEventInvariant, ← KnowableBy_serialize, Bytes.KnowableBy] at h
  simp only [CommMetaDataKnowable, ← KnowableBy_serialize, Bytes.KnowableBy]
  grind [canFlowTrans]

public theorem requestMessageProperties (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (requestResponseParticipantLabel (α := α) metadata.server)) metadata.request tr ∧
    IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) metadata.request tr ∧
    metadata.key.KnowableBy (requestResponseParticipantLabel (α := α) metadata.server) tr ∧
    ((∃ client, RequestResponseEventPredicates.sendRequest tr client metadata.server metadata.request (metadata.key.label tr) ∧
      requestResponseLabel (α := α) client metadata.server = metadata.key.label tr) ∨
      (metadata.key.Publishable tr ∧ IsWellFormed Bytes.Publishable metadata.request tr)) := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  have hm := deriveCommMetaDataKnowableServer tr htr metadata metadata.server hevent
  refine ⟨hm.2, h.2.1, hm.1, ?_⟩
  simp only [requestResponseEventInvariant, hclient] at h
  rcases h.2.2.2 with ⟨client, hs⟩ | hp
  · have hs := sendRequestEventProperties tr htr client metadata ⟨_, hs⟩
    exact Or.inl ⟨client, hs.2.2.2, hs.2.1⟩
  · exact Or.inr hp

public theorem requestMessageAuthenticatedProperties (tr : ProofTrace) (htr : tr.Invariant) (server : Participant) (metadata : AuthenticatedMetadata α)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest (some metadata.client) server metadata.request metadata.key : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (requestResponseParticipantLabel (α := α) server)) metadata.request tr ∧
    IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) metadata.request tr ∧
    metadata.key.KnowableBy (requestResponseParticipantLabel (α := α) server) tr ∧
    ((RequestResponseEventPredicates.sendRequest tr metadata.client server metadata.request (metadata.key.label tr) ∧
      requestResponseLabel (α := α) metadata.client server = metadata.key.label tr) ∨
      (participantCommunicationCompromised (α := WireMessage α) metadata.client tr.erase ∧
        metadata.key.Publishable tr ∧ IsWellFormed Bytes.Publishable metadata.request tr)) := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  have hm := deriveCommMetaDataKnowableServer tr htr metadata.toMetadata server hevent
  refine ⟨hm.2, h.2.1, hm.1, ?_⟩
  rcases h.2.2.2 with hs | hp
  · have hs := sendRequestEventProperties tr htr metadata.client {metadata.toMetadata with server := server} ⟨_, hs⟩
    exact Or.inl ⟨hs.2.2.2, hs.2.1⟩
  · exact Or.inr hp

public theorem sendResponseEventProperties (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (response : α)
    (hevent : tr.erase.EventLogged (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key : RequestResponseEvent α)) :
    tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α) ∧
    IsWellFormed Bytes.WellFormed metadata.request tr ∧ IsWellFormed Bytes.WellFormed response tr ∧
    metadata.key.WellFormed tr ∧
    RequestResponseEventPredicates.sendResponse tr metadata.client metadata.server metadata.request response (metadata.key.label tr) := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  exact ⟨h.1, h.2.1, h.2.2.1, (by have := h.2.2.2.1; grind), h.2.2.2.2⟩

public theorem responseMessageProperties (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client metadata.server)) response tr ∧
    (tr.erase.EventLogged (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key : RequestResponseEvent α) ∨
      (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
      (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase) ∧
    RequestResponseEventPredicates.sendRequest tr client metadata.server metadata.request (metadata.key.label tr) ∧
    (RequestResponseEventPredicates.sendResponse tr metadata.client metadata.server metadata.request response (metadata.key.label tr) ∨
      (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
      (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase) := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  have hs := sendRequestEventProperties tr htr client metadata ⟨_, h.2.2.2.1⟩
  refine ⟨h.1, h.2.2.2.2.1, hs.2.2.2, ?_⟩
  exact h.2.2.2.2.1.imp (fun he => (sendResponseEventProperties tr htr metadata response he).2.2.2.2) id

public theorem requestMessagePropertiesRequest (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (requestResponseParticipantLabel (α := α) metadata.server)) metadata.request tr := by
  have h := requestMessageProperties tr htr metadata hclient hevent
  exact h.1

public theorem requestMessagePropertiesRequest' (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (metadata.key.label tr)) metadata.request tr := by
  have h := requestMessageProperties tr htr metadata hclient hevent
  exact h.2.1

public theorem requestMessagePropertiesKey (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    metadata.key.KnowableBy (requestResponseParticipantLabel (α := α) metadata.server) tr := by
  have h := requestMessageProperties tr htr metadata hclient hevent
  exact h.2.2.1

public theorem requestMessagePropertiesKeyWellFormed (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    metadata.key.WellFormed tr := by
  have h := requestMessageProperties tr htr metadata hclient hevent
  exact by have := h.2.2.1; grind

public theorem requestMessagePropertiesSendRequest (tr : ProofTrace) (htr : tr.Invariant) (metadata : CommunicationMetadata α) (hclient : metadata.client = none)
    (hevent : tr.erase.EventLogged (.serverReceiveRequest metadata.client metadata.server metadata.request metadata.key : RequestResponseEvent α)) :
    (∃ client, RequestResponseEventPredicates.sendRequest tr client metadata.server metadata.request (metadata.key.label tr)) ∨
    (metadata.key.Publishable tr ∧ IsWellFormed Bytes.Publishable metadata.request tr) := by
  have h := requestMessageProperties tr htr metadata hclient hevent
  exact h.2.2.2.imp (fun ⟨client, hp, _⟩ => ⟨client, hp⟩) id

public theorem responseMessagePropertiesSendEvent (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    tr.erase.EventLogged (.serverSendResponse metadata.client metadata.server metadata.request response metadata.key : RequestResponseEvent α) ∨
    (metadata.key.Publishable tr ∧ IsWellFormed Bytes.Publishable response tr ∧
      ((requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
        (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase)) := by
  have h := requestResponseEventInvariant_of_logged _ tr htr hevent
  rcases h.2.2.2.2.1 with hs | hc
  · exact Or.inl hs
  · refine Or.inr ⟨?_, ?_, hc⟩
    · simp only [Bytes.Publishable, h.2.2.1, ← canFlowPubEqIsCorrupt, requestResponseLabel, Label.joinIsCorrupt]
      exact ⟨h.2.1, hc⟩
    · have hr := h.1
      simp only [← KnowableBy_serialize, Bytes.KnowableBy] at hr
      simp only [← Publishable_serialize, Bytes.Publishable]
      have hc' : (requestResponseLabel (α := α) client metadata.server).canFlow Label.pub tr.erase := by
        simpa only [← canFlowPubEqIsCorrupt, requestResponseLabel, Label.joinIsCorrupt] using hc
      exact ⟨hr.1, canFlowTrans _ _ _ _ hr.2 hc'⟩

public theorem responseMessagePropertiesPayload (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    IsWellFormed (Bytes.KnowableBy (requestResponseLabel (α := α) client metadata.server)) response tr := by
  have h := responseMessageProperties tr htr client response metadata hevent
  exact h.1

public theorem responseMessagePropertiesSendRequest (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    RequestResponseEventPredicates.sendRequest tr client metadata.server metadata.request (metadata.key.label tr) := by
  have h := responseMessageProperties tr htr client response metadata hevent
  exact h.2.2.1

public theorem responseMessagePropertiesSendResponse (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    RequestResponseEventPredicates.sendResponse tr metadata.client metadata.server metadata.request response (metadata.key.label tr) ∨
    (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
    (requestResponseParticipantLabel (α := α) metadata.server).isCorrupt tr.erase := by
  have h := responseMessageProperties tr htr client response metadata hevent
  exact h.2.2.2

public theorem responseMessagePropertiesSendResponse' (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (response : α) (metadata : CommunicationMetadata α)
    (hevent : tr.erase.EventLogged (.clientReceiveResponse client response metadata : RequestResponseEvent α)) :
    RequestResponseEventPredicates.sendResponse tr metadata.client metadata.server metadata.request response (metadata.key.label tr) ∨
    (metadata.key.Publishable tr ∧ IsWellFormed Bytes.Publishable response tr) := by
  rcases responseMessagePropertiesSendEvent tr htr client response metadata hevent with hs | hp
  · exact Or.inl (sendResponseEventProperties tr htr metadata response hs).2.2.2.2
  · exact Or.inr ⟨hp.1, hp.2.1⟩

section KeySecrecy

omit [BytesFunctor.Has Random.SubF] [RequestResponseEventPredicates α]
omit [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]
omit [TraceInvariant.Has (ProtocolEvent.ProofEntryT (RequestResponseEvent α))]

variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
attribute [local instance] communicationStateInv
variable [ProofTraceTypes.Has (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]
variable [TraceInvariant.Has (PersistentLocalUpdateableState.CompromisableState.ProofEntryT (CommunicationState α))]

/-- Every historical communication state satisfies the persistent state invariant. -/
public theorem communicationStateInvariant_of_stored
  (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (state : CommunicationState α) (stateId : Nat)
  (hst : PersistentLocalUpdateableState.StateWasSet tr.erase client stateId state) :
  requestResponseStateInvariant client state tr
:= by
  exact PersistentLocalUpdateableState.stateWasSet_implies_pred tr client stateId state htr hst

variable [AttackerKnowledge] [BaseAttackerKnowledge] [AttackerKnowledgeTheorem] [BaseAttackerKnowledgeTheorem]

public theorem keySecrecyClient (tr : ProofTrace) (htr : tr.Invariant) (client : Participant) (clientOpt : Option Participant) (server : Participant) (key : Bytes) (request response : α)
    (hknows : key.AttackerKnows tr.erase)
    (hst : (∃ stateId, PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest {client := clientOpt, server, request, key} : CommunicationState α)) ∨
      (∃ stateId, PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientReceiveResponse {server, response, key} : CommunicationState α))) :
    (requestResponseParticipantLabel (α := α) client).isCorrupt tr.erase ∨
    (requestResponseParticipantLabel (α := α) server).isCorrupt tr.erase := by
  have hp := Bytes.AttackerKnows_implies_Publishable key tr htr hknows
  have hl : key.label tr = requestResponseLabel (α := α) client server := by
    rcases hst with ⟨handle, hs⟩ | ⟨handle, hs⟩
    · exact (communicationStateInvariant_of_stored tr htr client _ handle hs).2.2.1
    · exact (communicationStateInvariant_of_stored tr htr client _ handle hs).2.2
  simpa only [← canFlowPubEqIsCorrupt, hl, requestResponseLabel, Label.joinIsCorrupt] using hp.2

end KeySecrecy

end DY.Communication
