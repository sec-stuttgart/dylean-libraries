module

public import Examples.Login.Reachability
import all Examples.Login.Invariants

namespace DY.Example.Login

public section

/-- A server's successful password check has a preceding matching client start,
unless either endpoint’s credentials, communication keys, or communication state
were already compromised. -/
theorem serverAuthentication
  (client server : Participant) (password cookie : Bytes) (time : Nat) :
  ∀ tr : ExecTrace, tr.Reachable reachability →
    tr.EventLoggedAt (.authenticated client server password cookie : LoginEvent) time →
    (tr.prefix time).EventLogged (.started client server password : LoginEvent) ∨ Compromised client server (tr.prefix time)
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr htr he
  have h := Trace.EventLoggedAt_imp_EventInv _ time tr htr he
  simpa only [ProtocolEvent.EventInv.invariant, Trace.prefix_erase] using h.2.2

/-- Receiving a cookie authenticates a preceding server acceptance of that same
client and cookie, unless endpoint credentials, communication keys, or communication
state were compromised before receipt. -/
theorem clientAuthentication
  (client server : Participant) (cookie : Bytes) (time : Nat) :
  ∀ tr : ExecTrace, tr.Reachable reachability →
    tr.EventLoggedAt (.cookieReceived client server cookie : LoginEvent) time →
    (∃ password, (tr.prefix time).EventLogged (.authenticated client server password cookie : LoginEvent)) ∨ Compromised client server (tr.prefix time)
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr htr he
  have h := Trace.EventLoggedAt_imp_EventInv _ time tr htr he
  simpa only [ProtocolEvent.EventInv.invariant, Trace.prefix_erase] using h.2

/-- Provisioned passwords remain unknown to the network attacker while both
participants' credential states, communication keys, and session states remain uncompromised. -/
theorem passwordSecrecy
  (client server : Participant) (password : Bytes) (time : Nat) :
  ∀ tr : ExecTrace, tr.Reachable reachability →
    tr.EventLoggedAt (.provisioned client server password : LoginEvent) time →
    password.AttackerKnows tr →
    Compromised client server tr
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr htr he hk
  have hs := Trace.EventLoggedAt_imp_EventInv _ time tr htr he
  change PasswordSecret client server password (tr.prefix time) at hs
  exact passwordPublishable client server password tr (PasswordSecret.later _ _ _ _ _ (by grind) hs) (Bytes.AttackerKnows_implies_Publishable password tr htr hk)

/-- A cookie in either a server authentication event or a client receipt event
is secret unless endpoint credentials, communication keys, or communication state
are compromised, including exposure after the event. -/
theorem cookieSecrecy
  (client server : Participant) (cookie : Bytes) (time : Nat) :
  ∀ tr : ExecTrace, tr.Reachable reachability →
    ((∃ password, tr.EventLoggedAt (.authenticated client server password cookie : LoginEvent) time) ∨ tr.EventLoggedAt (.cookieReceived client server cookie : LoginEvent) time) →
    cookie.AttackerKnows tr →
    Compromised client server tr
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr htr he hk
  have hs : CookieSecret client server cookie (tr.prefix time) := by
    rcases he with ⟨password, he⟩ | he
    · exact (Trace.EventLoggedAt_imp_EventInv _ time tr htr he).2.1
    · exact (Trace.EventLoggedAt_imp_EventInv _ time tr htr he).1
  have hc : CookieSecret client server cookie tr := CookieSecret.later _ _ _ _ _ (by grind) hs
  rcases hc with hs | hc
  · exact secretPublishable client server cookie tr hs (Bytes.AttackerKnows_implies_Publishable cookie tr htr hk)
  · exact hc

/-- info: 'DY.Example.Login.serverAuthentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms serverAuthentication

/-- info: 'DY.Example.Login.clientAuthentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clientAuthentication

/-- info: 'DY.Example.Login.passwordSecrecy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms passwordSecrecy

/-- info: 'DY.Example.Login.cookieSecrecy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cookieSecrecy

end
end DY.Example.Login
