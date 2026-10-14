module

public import Login.Invariants
import all Login.Specification
import all Login.Invariants
import all DyLibraries.Communication.RequestResponse.Invariants
import all DyLibraries.Communication.RequestResponse
import DY.Meta.Step

namespace DY.Example.Login

open DY.Comparse DY.Communication

public section

theorem secretPublishable (client server : Participant) (secret : Bytes) (tr : ProofTrace) (hs : Secret client server secret tr) (hp : secret.Publishable tr) : Compromised client server tr.erase := by
  simp only [Compromised, passwordLabel, Label.joinIsCorrupt]
  apply Or.inr
  simpa only [← canFlowPubEqIsCorrupt, hs.2] using hp.2

/-- Publishing a provisioned password implies credential-state or communication compromise. -/
theorem passwordPublishable
  (client server : Participant) (password : Bytes) (tr : ProofTrace)
  (hs : PasswordSecret client server password tr) (hp : password.Publishable tr) :
  Compromised client server tr.erase
:= by
  simpa only [Compromised, ← canFlowPubEqIsCorrupt, hs.2] using hp.2

theorem authenticatedInvariant (client server : Participant) (password cookie : Bytes) (tr : ProofTrace) (htr : tr.Invariant) (he : tr.erase.EventLogged (.authenticated client server password cookie : LoginEvent)) : PasswordSecret client server password tr ∧ CookieSecret client server cookie tr ∧ (tr.erase.EventLogged (.started client server password : LoginEvent) ∨ Compromised client server tr.erase) := by
  obtain ⟨i, hi⟩ := Trace.EventLogged_imp_EventInv _ tr htr he
  simp only [ProtocolEvent.EventInv.invariant] at hi
  grind

theorem checkedRequest (tr : ProofTrace) (htr : tr.Invariant) (client server : Participant) (password : Bytes) (metadata : CommunicationMetadata Payload) (hs : PasswordSecret client server password tr) (hc : metadata.client = none) (hserver : metadata.server = server) (hclient : metadata.request.client = client) (hpassword : metadata.request.secret = password) (he : tr.erase.EventLogged (.serverReceiveRequest none server metadata.request metadata.key : RequestResponseEvent Payload)) : (tr.erase.EventLogged (.started client server password : LoginEvent) ∧ metadata.key.label tr = sharedLabel client server) ∨ Compromised client server tr.erase := by
  have hp := requestMessageProperties tr htr metadata hc (by simpa [hc, hserver] using he)
  rcases hp.2.2.2 with ⟨sender, hsend, hlabel⟩ | hpub
  · simp only [RequestResponseEventPredicates.sendRequest] at hsend
    left
    grind
  · right
    apply passwordPublishable client server password tr hs
    simpa [hpassword] using hpub.2

@[instance] theorem provision.proof (client server : Participant) : HoareTriple (provision client server) (fun _ => True) (fun _ _ => True) := by
  unfold provision
  step with ⟨fun _ => passwordLabel client server, Usage.nothing⟩
  step by simp only [ProtocolEvent.EventInv.invariant, PasswordSecret]; grind
  dsimp only
  step by simp only [PersistentLocalState.LocalStateInv.invariant, PasswordSecret]; grind
  step by simp only [PersistentLocalState.LocalStateInv.invariant, PasswordSecret]; grind
  step
  trivial

@[instance] theorem Client.start.proof (client : Participant) (stateHandle : Nat) (keys : CommunicationKeyHandles) : HoareTriple (Client.start client stateHandle keys) (fun _ => True) (fun _ _ => True) := by
  unfold Client.start
  step
  step
  step by simp_all only [PersistentLocalState.LocalStateInv.invariant, ProtocolEvent.EventInv.invariant]
  step by
    simp_all only [PersistentLocalState.LocalStateInv.invariant, RequestResponseEventPredicates.sendRequest, Payload.IsWellFormed_eq, PasswordSecret]
    have hflow := Label.joinCanFlowRight (stateLabel client st.server) (sharedLabel client st.server) tr.erase
    grind [Bytes.KnowableBy, passwordLabel]
  trivial

@[instance] theorem Server.authenticate.proof (server : Participant) (stateHandle : Nat) (keys : CommunicationKeyHandles) (messageHandle : Nat) : HoareTriple (Server.authenticate server stateHandle keys messageHandle) (fun _ => True) (fun _ _ => True) := by
  apply HoareTriple.mk
  intro tr _ htr
  unfold Server.authenticate
  step
  rename_i st hst
  step
  rename_i hserver
  step
  rename_i result hpost
  obtain ⟨metadata, hreceived, hn, hr⟩ := hpost
  have hs := hreceived.2.1
  have he := hreceived.2.2.2
  split
  rename_i request stateId
  step
  expose_names
  have hsecret : PasswordSecret st.client server st.password tr := by simp_all only [PersistentLocalState.LocalStateInv.invariant]
  have hkey : metadata.key.Invariant tr := (requestMessagePropertiesKey tr htr metadata hn (by grind)).1
  have hchecked := checkedRequest tr htr st.client server st.password metadata hsecret hn hs (by grind) (by grind) (by grind)
  step with ⟨fun _ => metadata.key.label tr, ({type := "Nonce", tag := "Login.Cookie", data := serialize ("" : String)} : Usage)⟩
  step by
    simp_all only [ProtocolEvent.EventInv.invariant, CookieSecret, Secret]
    grind
  step by
    refine ⟨metadata, ?_⟩
    simp only [RequestResponseEventPredicates.sendResponse, Payload.IsWellFormed_eq]
    grind [Bytes.KnowableBy]
  trivial

@[instance] theorem Client.finish.proof (client : Participant) (stateId : Nat) (messageHandle : Nat) : HoareTriple (Client.finish client stateId messageHandle) (fun _ => True) (fun _ _ => True) := by
  apply HoareTriple.mk
  intro tr _ htr
  unfold Client.finish
  step
  rename_i state hrecent hstate
  have hw : PersistentLocalUpdateableState.StateWasSet tr.erase client stateId state := by
    obtain ⟨time, hw, _⟩ := PersistentLocalUpdateableState.isMostRecentStateFor_spec client stateId state tr.erase hrecent
    exact ⟨time, hw⟩
  clear hrecent
  split
  · expose_names
    let metadata : CommunicationMetadata Payload := {client := sent.client, server := sent.server, request := sent.request, key := sent.key, stateHandle := stateId}
    have hstored : (metadata.stateHandle = stateId ∧ PersistentLocalUpdateableState.StateWasSet tr.erase client stateId (.clientSendRequest ⟨metadata.client, metadata.server, metadata.request, metadata.key⟩ : CommunicationState _)) := by simp_all [metadata]
    step
    rename_i response he
    obtain ⟨received, hstoredReceived, he⟩ := he
    have heq := clientMetadata_unique tr client stateId received metadata htr hstoredReceived (by assumption)
    subst received
    step
    step by
      expose_names
      have hp := responseMessageProperties tr htr client response metadata (by grind)
      have hcorr : (requestResponseParticipantLabel (α := Payload) client).isCorrupt tr.erase ∨ (requestResponseParticipantLabel (α := Payload) metadata.server).isCorrupt tr.erase → Compromised client metadata.server tr.erase := by
        simp only [Compromised, passwordLabel, sharedLabel, requestResponseLabel, Label.joinIsCorrupt]
        exact Or.inr
      have hlogin : CookieSecret client metadata.server response.secret tr ∧ ((∃ password, tr.erase.EventLogged (.authenticated client metadata.server password response.secret : LoginEvent)) ∨ Compromised client metadata.server tr.erase) := by
        rcases hp.2.2.2 with hs | hc
        · simp only [RequestResponseEventPredicates.sendResponse] at hs
          have ha : tr.erase.EventLogged (.authenticated client metadata.server metadata.request.secret response.secret : LoginEvent) := by grind
          exact ⟨(authenticatedInvariant _ _ _ _ tr htr ha).2.1, Or.inl ⟨_, ha⟩⟩
        · exact ⟨Or.inr (hcorr hc), Or.inr (hcorr hc)⟩
      exact hlogin
    step
    trivial
  · simp [wp, Traceful.run_failure]; exact ⟨tr, htr, rfl, by grind⟩

end
end DY.Example.Login
