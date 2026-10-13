module

public import Examples.Login.Proof
import all Examples.Login.Specification
import all Examples.Login.Invariants
import DY.Meta.Step

namespace DY.Example.Login

open DY.Communication

public section

def initializeKeys (client server : Participant) : Traceful (CommunicationKeyHandles × CommunicationKeyHandles) := initializeRequestResponse (α := Payload) client server

def compromiseSession (participant : Participant) (stateId : Nat) : Traceful Nat := compromiseCommunicationState (α := Payload) participant stateId

/-- Disclose the credentials retained at a persistent state handle. -/
def compromiseCredentials (stateHandle : Nat) : Traceful Nat := PersistentLocalState.compromise Credentials stateHandle

/-- Credential disclosure preserves the invariant with its explicit compromise exception. -/
@[instance]
theorem compromiseCredentials.proof
  (stateHandle : Nat) :
  HoareTriple (compromiseCredentials stateHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromiseCredentials
  step
  trivial

@[expose] def compromiseCredentials.reachability : ReachabilityConfig := .make compromiseCredentials

instance : ReachableImpliesInvariant compromiseCredentials.reachability := .mk compromiseCredentials.proof

@[instance] theorem initializeKeys.proof (client server : Participant) : HoareTriple (initializeKeys client server) (fun _ => True) (fun _ _ => True) := initializeRequestResponse.proof client server

@[instance] theorem compromiseSession.proof (participant : Participant) (stateId : Nat) : HoareTriple (compromiseSession participant stateId) (fun _ => True) (fun _ _ => True) := by
  unfold compromiseSession
  step
  trivial

@[expose] def provision.reachability : ReachabilityConfig := .make (fun (client, server) => provision client server)
@[expose] def initializeKeys.reachability : ReachabilityConfig := .make (fun (client, server) => initializeKeys client server)
@[expose] def Client.start.reachability : ReachabilityConfig := .make (fun (client, handle, keys) => Client.start client handle keys)
@[expose] def Server.authenticate.reachability : ReachabilityConfig := .make (fun (server, handle, keys, message) => Server.authenticate server handle keys message)
@[expose] def Client.finish.reachability : ReachabilityConfig := .make (fun (client, metadata, message) => Client.finish client metadata message)
@[expose] def compromiseSession.reachability : ReachabilityConfig := .make (fun (participant, stateId) => compromiseSession participant stateId)

#combine into ReachabilityConfig from
  Network,
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  provision,
  initializeKeys,
  Client.start,
  Server.authenticate,
  Client.finish,
  compromiseSession,
  compromiseCredentials,

instance : ReachableImpliesInvariant provision.reachability := .mk (fun (client, server) => provision.proof client server)
instance : ReachableImpliesInvariant initializeKeys.reachability := .mk (fun (client, server) => initializeKeys.proof client server)
instance : ReachableImpliesInvariant Client.start.reachability := .mk (fun (client, handle, keys) => Client.start.proof client handle keys)
instance : ReachableImpliesInvariant Server.authenticate.reachability := .mk (fun (server, handle, keys, message) => Server.authenticate.proof server handle keys message)
instance : ReachableImpliesInvariant Client.finish.reachability := .mk (fun (client, metadata, message) => Client.finish.proof client metadata message)
instance : ReachableImpliesInvariant compromiseSession.reachability := .mk (fun (participant, stateId) => compromiseSession.proof participant stateId)

#combine into ReachabilityTheorem from
  Network,
  LongTermKeys (pkeKeyName (WireMessage Payload)),
  LongTermKeys (signatureKeyName (WireMessage Payload)),
  provision,
  initializeKeys,
  Client.start,
  Server.authenticate,
  Client.finish,
  compromiseSession,
  compromiseCredentials,

end
end DY.Example.Login
