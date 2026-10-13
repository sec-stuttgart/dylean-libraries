module

public import DY.Communication.Core.Lemmas
import all DY.Communication.Core
import all DY.Communication.Core.Invariants
import all DY.Comparse

namespace DY.Communication

open DY.Comparse

variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF] [BytesFunctor.Has Signature.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]
variable [HigherLayerEventPredicates α] [TraceInvariant]
attribute [local instance] coreEventInv
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (CoreEvent α))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (CoreEvent α))]

public theorem coreEventInvariant_of_logged (event : CoreEvent α) (tr : ProofTrace) (htr : tr.Invariant)
    (hevent : tr.erase.EventLogged event) : coreEventInvariant tr event := by
  obtain ⟨i, h⟩ := Trace.EventLogged_imp_EventInv event tr htr hevent
  exact coreEventInvariant_later event _ tr (by grind) h

/-- The receiver's principal label is represented by its communication key label
(`communicationLabel receiver receiver`) in the Core port. -/
public theorem confMessageProperties (tr : ProofTrace) (htr : tr.Invariant) (sender receiver : Participant) (payload : α)
    (hevent : tr.erase.EventLogged (.confidentialReceive sender receiver payload : CoreEvent α)) :
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) receiver receiver)) payload tr ∧
    (HigherLayerEventPredicates.confidential tr sender receiver payload ∨ IsWellFormed Bytes.Publishable payload tr) := by
  have h := coreEventInvariant_of_logged _ tr htr hevent
  change tr.erase.EventLogged (.confidentialSend sender receiver payload : CoreEvent α) ∨ _ at h
  rcases h with hsend | hpub
  · have hs := coreEventInvariant_of_logged _ tr htr hsend
    refine ⟨?_, Or.inl hs.2⟩
    apply IsWellFormed_KnowableBy_canFlow _ _ _ _ _ hs.1
    simp only [Label.canFlow, communicationLabel]
    grind [canFlowTrans]
  · simp only [← KnowableBy_serialize, ← Publishable_serialize] at hpub ⊢
    grind [canFlowTrans]

omit [BytesInvariantsProofs] in
public theorem senderAuthentication (tr : ProofTrace) (i : Nat) (htr : tr.Invariant) (sender receiver : Participant) (payload : α)
    (hevent : tr.erase.EventLoggedAt (.authenticatedReceive sender receiver payload : CoreEvent α) i) :
    (tr.prefix i).erase.EventLogged (.authenticatedSend sender receiver payload : CoreEvent α) ∨
    participantCommunicationCompromised (α := α) sender (tr.prefix i).erase := by
  exact (Trace.EventLoggedAt_imp_EventInv _ i tr htr hevent).2

public theorem authenticatedMessageProperties (tr : ProofTrace) (htr : tr.Invariant) (sender receiver : Participant) (payload : α)
    (hevent : tr.erase.EventLogged (.authenticatedReceive sender receiver payload : CoreEvent α)) :
    IsWellFormed Bytes.Publishable payload tr ∧
    (HigherLayerEventPredicates.authenticated tr sender receiver payload ∨ participantCommunicationCompromised (α := α) sender tr.erase) := by
  have h := coreEventInvariant_of_logged _ tr htr hevent
  refine ⟨h.1, ?_⟩
  rcases h.2 with hsend | hcorrupt
  · exact Or.inl (coreEventInvariant_of_logged _ tr htr hsend).2
  · exact Or.inr hcorrupt

omit [BytesInvariantsProofs] in
public theorem senderConfauthAuthentication (tr : ProofTrace) (i : Nat) (htr : tr.Invariant) (sender receiver : Participant) (payload : α)
    (hevent : tr.erase.EventLoggedAt (.confidentialAuthenticatedReceive sender receiver payload : CoreEvent α) i) :
    (tr.prefix i).erase.EventLogged (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α) ∨
    participantCommunicationCompromised (α := α) sender (tr.prefix i).erase := by
  exact (Trace.EventLoggedAt_imp_EventInv _ i tr htr hevent).1

public theorem confAuthMessageProperties (tr : ProofTrace) (htr : tr.Invariant) (sender receiver : Participant) (payload : α)
    (hevent : tr.erase.EventLogged (.confidentialAuthenticatedReceive sender receiver payload : CoreEvent α)) :
    IsWellFormed (Bytes.KnowableBy (communicationLabel (α := α) sender receiver)) payload tr ∧
    (HigherLayerEventPredicates.confidentialAuthenticated tr sender receiver payload ∨
      (participantCommunicationCompromised (α := α) sender tr.erase ∧ IsWellFormed Bytes.Publishable payload tr)) := by
  have h := coreEventInvariant_of_logged _ tr htr hevent
  by_cases hs : tr.erase.EventLogged (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α)
  · have hsend := coreEventInvariant_of_logged _ tr htr hs
    exact ⟨hsend.1, Or.inl hsend.2⟩
  · have hpub := h.2.resolve_left hs
    refine ⟨?_, Or.inr ⟨h.1.resolve_left hs, hpub⟩⟩
    simp only [← KnowableBy_serialize, ← Publishable_serialize] at hpub ⊢
    grind [canFlowTrans]

end DY.Communication
