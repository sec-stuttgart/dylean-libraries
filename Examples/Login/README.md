# Login over confidential request/response

Import `Examples.Login.All` to load the example and its executable checks.

`provision client server` generates a symbolic password and stores matching
`Credentials` at both endpoints. It returns their persistent state handles.
`initializeKeys client server` establishes the communication key handles.

1. `Client.start` reads its credentials, logs `LoginEvent.started`, and sends
   a confidential request containing its client identifier and password.
2. `Server.authenticate` reads its credentials and checks the request kind,
   client identifier, and password. Only after all checks succeed does it
   generate a fresh nonce, log `LoginEvent.authenticated`, and send the cookie
   in an encrypted response.
3. `Client.finish` checks the response through the request/response library,
   validates its kind and client identifier, logs `LoginEvent.cookieReceived`,
   and returns the cookie.

Requests use `sendRequest`, without client signatures. Client authentication
therefore follows from the password comparison and password secrecy. Cookies
use `makeResponseNonce` and inherit the response key's secrecy label. The
request/response predicates bind outgoing messages to the login events.

## Files

- `Specification.lean`: concrete byte and execution configuration, message
  formats, provisioned credentials, events, and executable roles.
- `Invariants.lean`: concrete cryptographic predicates, credential and event
  invariants, compromise labels, and the global proof configuration.
- `Proof.lean`: invariant-preserving Hoare specifications, composed with `step`.
- `Reachability.lean`: arbitrary interleavings of provisioning, roles, network
  attacker actions, key registration/compromise, credential-state compromise,
  and session-state compromise.
- `SecurityTheorems.lean`: security over reachable execution traces, with
  checked axiom lists for each theorem.
- `SanityChecks.lean`: successful execution, fresh cookies, replay behavior,
  and rejection of wrong passwords, client identifiers, and recipients.

## Security statements and assumptions

`serverAuthentication` proves that an authentication event has a matching
client start in its strict trace prefix. `clientAuthentication` proves that a
cookie-receive event has a server authentication event for the same client,
server, and cookie in its strict trace prefix. Both allow endpoint compromise
before the corresponding event.

`passwordSecrecy` and `cookieSecrecy` prove that
attacker knowledge of the corresponding secret implies endpoint compromise.
For secrecy, compromise is evaluated on the full trace, including later
exposure of communication state. `Compromised` means exposure of either
participant's stored credentials, communication keys, or request/response state.
Passwords use a label that joins credential-state and communication exposure;
cookies retain the communication label, with credential compromise also allowed
as an authentication exception.

Provisioning is trusted and passwords are modeled as unguessable symbolic
secrets. Credential storage uses `PersistentLocalState.CompromisableState`. The reachable
`compromiseCredentials stateHandle` action publishes the stored credentials,
including the password. This example does not model password hashing or
dictionary attacks. Communication
state containing passwords, cookies, or response keys can be compromised.
Protocol events are proof observations, not public network messages.

Authentication is non-injective: replay is permitted. A replayed request may
produce another fresh cookie; a replayed response returns the original cookie.
The protocol does not implement replay caches, expiration, or logout.

Run `lake build Examples.Login.All` for the example, or `lake build` for the
whole project. All implementation files are contained in this directory.
