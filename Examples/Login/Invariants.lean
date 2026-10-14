module

public import Login.Specification
import all Login.Specification
import DY.Meta.Step

namespace DY.Example.Login

open DY.Comparse DY.Communication

public section

#combine +toplevel into ProofEntryT from
  Network,
  Random,
  ProtocolEvent LoginEvent,
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),
  PersistentLocalState.CompromisableState Credentials,

abbrev sharedLabel (client server : Participant) : Label := requestResponseLabel (α := Payload) client server

/-- Exposure of any login state owned by either endpoint compromises their stored credentials. -/
def stateLabel
  (client server : Participant) :
  Label
:=
  { isCorrupt := fun tr => ∃ participant state, (participant = client ∨ participant = server) ∧ PersistentLocalState.LocalStateCompromised participant (state : Credentials) tr
    isCorruptLater := by
      rintro tr1 tr2 later ⟨participant, state, owner, compromised⟩
      exact ⟨participant, state, owner, PersistentLocalState.LocalStateCompromised_le participant state tr1 tr2 later compromised⟩ }

/-- Passwords can be exposed by login-state compromise or communication compromise. -/
def passwordLabel (client server : Participant) : Label := (stateLabel client server).join (sharedLabel client server)

/-- Either endpoint's concrete credential-state label permits disclosure of their password. -/
theorem passwordLabel_canFlow_state
  (client server participant : Participant) (state : Credentials) (tr : ExecTrace) :
  participant = client ∨ participant = server →
    (passwordLabel client server).canFlow (PersistentLocalState.label participant state) tr
:= by
  unfold Label.canFlow
  intro owner later _ compromised
  simp only [passwordLabel, Label.joinIsCorrupt, stateLabel]
  exact Or.inl ⟨participant, state, owner, (PersistentLocalState.label_isCorrupt participant state later).mp compromised⟩

/-- Either endpoint's login state, communication keys, or communication state was exposed. -/
def Compromised (client server : Participant) (tr : ExecTrace) : Prop := (passwordLabel client server).isCorrupt tr

/-- Endpoint compromise persists as the execution trace grows. -/
theorem Compromised.later (client server : Participant) (tr₁ tr₂ : ExecTrace) : tr₁ ≤ tr₂ → Compromised client server tr₁ → Compromised client server tr₂ := by
  unfold Compromised
  grind

grind_pattern Compromised.later => tr₁ ≤ tr₂, Compromised client server tr₁
grind_pattern [grind_later] Compromised.later => tr₁ ≤ tr₂, Compromised client server tr₁

instance [BytesWellFormed] : RequestResponseEventPredicates Payload where
  sendRequest tr client server request _ := request.kind = "request" ∧ request.client = client ∧ tr.erase.EventLogged (.started client server request.secret : LoginEvent)
  sendResponse tr _ server request response _ := response.kind = "cookie" ∧ response.client = request.client ∧ tr.erase.EventLogged (.authenticated request.client server request.secret response.secret : LoginEvent)
  sendRequest_later := by grind
  sendResponse_later := by grind

instance : PublicKeyEncryption.EncryptPred := corePkeEncryptPred (WireMessage Payload)
instance [BytesInvariants] [BytesInvariants.Has PublicKeyEncryption.Pk.invariants] : PublicKeyEncryption.EncryptPredProof := corePkeEncryptPredProof (WireMessage Payload) rfl
instance : Signature.SignPred := coreSignPred (WireMessage Payload)
instance [BytesInvariants] : Signature.SignPredProof := coreSignPredProof (WireMessage Payload) rfl
instance : AEAD.EncryptPred := requestResponseAEADPredicate (α := Payload)
instance [BytesInvariants] : AEAD.EncryptPredProof := requestResponseAEADPredicateProof (α := Payload) rfl

#combine +toplevel into BytesInvariants, BytesInvariantsProofs from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

def Secret (client server : Participant) (secret : Bytes) (tr : ProofTrace) : Prop := secret.Invariant tr ∧ secret.label tr = sharedLabel client server

theorem Secret.later (client server : Participant) (secret : Bytes) (tr₁ tr₂ : ProofTrace) : tr₁ ≤ tr₂ → Secret client server secret tr₁ → Secret client server secret tr₂ := by
  unfold Secret
  grind

grind_pattern Secret.later => tr₁ ≤ tr₂, Secret client server secret tr₁
grind_pattern [grind_later] Secret.later => tr₁ ≤ tr₂, Secret client server secret tr₁

/-- A password retains its byte invariant and the joined state/communication label. -/
def PasswordSecret (client server : Participant) (password : Bytes) (tr : ProofTrace) : Prop := password.Invariant tr ∧ password.label tr = passwordLabel client server

/-- Password secrecy obligations persist as the trace grows. -/
theorem PasswordSecret.later
  (client server : Participant) (password : Bytes) (tr₁ tr₂ : ProofTrace) :
  tr₁ ≤ tr₂ → PasswordSecret client server password tr₁ → PasswordSecret client server password tr₂
:= by
  unfold PasswordSecret
  grind

grind_pattern [grind_later] PasswordSecret.later => tr₁ ≤ tr₂, PasswordSecret client server password tr₁
grind_pattern PasswordSecret.later => tr₁ ≤ tr₂, PasswordSecret client server password tr₁

/-- A password can be disclosed under either endpoint's concrete login-state compromise label. -/
theorem passwordSecret_knowableBy_state
  (client server participant : Participant) (password : Bytes) (state : Credentials) (tr : ProofTrace) :
  PasswordSecret client server password tr →
    (participant = client ∨ participant = server) →
    password.KnowableBy (PersistentLocalState.label participant state) tr
:= by
  intro secret owner
  exact ⟨secret.1, secret.2 ▸ passwordLabel_canFlow_state client server participant state tr.erase owner⟩

def CookieSecret (client server : Participant) (cookie : Bytes) (tr : ProofTrace) : Prop := Secret client server cookie tr ∨ Compromised client server tr.erase

theorem CookieSecret.later (client server : Participant) (cookie : Bytes) (tr₁ tr₂ : ProofTrace) : tr₁ ≤ tr₂ → CookieSecret client server cookie tr₁ → CookieSecret client server cookie tr₂ := by
  unfold CookieSecret
  grind

grind_pattern CookieSecret.later => tr₁ ≤ tr₂, CookieSecret client server cookie tr₁
grind_pattern [grind_later] CookieSecret.later => tr₁ ≤ tr₂, CookieSecret client server cookie tr₁

/-- Credentials belong to an endpoint and retain the exact password label. -/
instance : PersistentLocalState.LocalStateInv Credentials where
  invariant participant st tr := (participant = st.client ∨ participant = st.server) ∧ PasswordSecret st.client st.server st.password tr
  invariant_later := by grind

/-- Compromising stored credentials may disclose their password under its state label. -/
instance : PersistentLocalState.CompromisableLocalStateInv Credentials where
  toLocalStateInv := inferInstance
  invariant_implies_KnowableBy := by
    intro participant state tr hstate
    obtain ⟨owner, secret⟩ := hstate
    simpa only [Credentials.IsWellFormed_eq] using passwordSecret_knowableBy_state state.client state.server participant state.password state tr secret owner

instance : ProtocolEvent.EventInv LoginEvent where
  invariant tr ev := match ev with
    | .provisioned client server password => PasswordSecret client server password tr
    | .started client server password => PasswordSecret client server password tr
    | .authenticated client server password cookie => PasswordSecret client server password tr ∧ CookieSecret client server cookie tr ∧ (tr.erase.EventLogged (.started client server password : LoginEvent) ∨ Compromised client server tr.erase)
    | .cookieReceived client server cookie => CookieSecret client server cookie tr ∧ ((∃ password, tr.erase.EventLogged (.authenticated client server password cookie : LoginEvent)) ∨ Compromised client server tr.erase)

instance : LongTermKeys.ProofConfig (pkeKeyName (WireMessage Payload)) (fun _ => communicationPkeUsage (WireMessage Payload)) (LongTermKeys.label (pkeKeyName (WireMessage Payload))) := communicationPkeProofConfig (α := WireMessage Payload)

instance : LongTermKeys.ProofConfig (signatureKeyName (WireMessage Payload)) (fun _ => communicationSignatureUsage (WireMessage Payload)) (LongTermKeys.label (signatureKeyName (WireMessage Payload))) := communicationSignatureProofConfig (α := WireMessage Payload)
instance : PersistentLocalUpdateableState.CompromisableLocalStateInv (CommunicationState Payload) := communicationStateInv (α := Payload)
instance : ProtocolEvent.EventInv (CoreEvent (WireMessage Payload)) := coreEventInv (α := WireMessage Payload)
instance : ProtocolEvent.EventInv (RequestResponseEvent Payload) := requestResponseEventInv (α := Payload)

#combine +toplevel into SubTraceInvariant, SubBaseAttackerKnowledgeTheorem from
  Network,
  Random,
  ProtocolEvent LoginEvent,
  ProtocolEvent (CoreEvent (WireMessage Payload)),
  ProtocolEvent (RequestResponseEvent Payload),
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  PersistentLocalUpdateableState.CompromisableState (CommunicationState Payload),
  PersistentLocalState.CompromisableState Credentials,

#combine +toplevel into SubAttackerKnowledgeTheorem from
  Random,
  Literal,
  Concat,
  PublicKeyEncryption,
  Signature,
  AEAD,

end
end DY.Example.Login
