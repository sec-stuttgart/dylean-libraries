module

public import DyLibraries.Communication.Data
public import DyExtensions.EquationalTheory.PublicKeyEncryption
public import DY.EquationalTheory.Sign
public import DY.Actions.Network
public import DyExtensions.Actions.Random
public import DyExtensions.Actions.ProtocolEvent
public import DY.Actions.LongTermKeys

namespace DY.Communication

open DY.Comparse

public def pkeKeyName (α : Type) [CoreConfig α] : String :=
  CoreConfig.tag (α := α) ++ ".PKE"

public def signatureKeyName (α : Type) [CoreConfig α] : String :=
  CoreConfig.tag (α := α) ++ ".Signature"

public instance [BytesFunctor] [BytesFunctor.Has PublicKeyEncryption.SubF] [CoreConfig α] :
    LongTermKeys.ExecConfig (pkeKeyName α) PublicKeyEncryption.pk where

public instance [BytesFunctor] [BytesFunctor.Has Signature.SubF] [CoreConfig α] :
    LongTermKeys.ExecConfig (signatureKeyName α) Signature.vk where

/-- Handles required by one endpoint.  Secret handles belong to the endpoint;
public handles refer to its configured peer. -/
public structure CommunicationKeyHandles where
  ownPkeSecretKey : Nat
  peerPkePublicKey : Nat
  ownSignatureSecretKey : Nat
  peerSignaturePublicKey : Nat
deriving DecidableEq

public inductive CoreEvent (α : Type) where
  | confidentialSend (sender receiver : Participant) (payload : α)
  | confidentialReceive (sender receiver : Participant) (payload : α)
  | authenticatedSend (sender receiver : Participant) (payload : α)
  | authenticatedReceive (sender receiver : Participant) (payload : α)
  | confidentialAuthenticatedSend (sender receiver : Participant) (payload : α)
  | confidentialAuthenticatedReceive (sender receiver : Participant) (payload : α)
deriving DecidableEq

section Runtime

-- Declare shared typeclass assumptions for the runtime definitions below:
-- byte constructors and lengths, cryptographic primitives, payload serialization
-- and configuration, and trace entries for network, randomness, protocol events,
-- and long-term keys.
variable [BytesFunctor] [BytesLength]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesFunctor.Has PublicKeyEncryption.SubF]
variable [BytesFunctor.Has Signature.SubF]
variable [BytesFunctor.Has Random.SubF]
variable [ParseableSerializeable α] [CoreConfig α]
variable [ExecTraceTypes]
variable [ExecTraceTypes.Has Network.ExecEntryT]
variable [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (CoreEvent α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (pkeKeyName α))]
variable [ExecTraceTypes.Has (LongTermKeys.ExecEntryT (signatureKeyName α))]

-- TODO we should probably not expose these internal functions to the outside
@[expose] public def encryptMessage
    (receiverPublicKey nonce : Bytes)
    (sender receiver : Participant) (payload : α) : Bytes :=
  PublicKeyEncryption.encrypt receiverPublicKey nonce <|
    serialize (.unsigned sender receiver payload : EncryptionInput α)

@[expose] public def decryptMessage
    (receiverSecretKey encryptedMessage : Bytes) : Err (CommunicationMessage α) := do
  let plaintext ← PublicKeyEncryption.decrypt receiverSecretKey encryptedMessage
  let input : EncryptionInput α ← parse plaintext
  match input with
  | .unsigned sender receiver payload => pure { sender, receiver, payload }
  | .signed .. => failure

public def sendConfidential
    (handles : CommunicationKeyHandles)
    (sender receiver : Participant) (payload : α) : Traceful Nat := do
  let receiverPublicKey ← LongTermKeys.getPublicKey (pkeKeyName α)
    receiver handles.peerPkePublicKey
  let nonce ← Random.genRand 32
  ProtocolEvent.logEvent (.confidentialSend sender receiver payload : CoreEvent α)
  Network.sendMessage (encryptMessage receiverPublicKey nonce sender receiver payload)

public def receiveConfidential
    (handles : CommunicationKeyHandles)
    (receiver : Participant) (messageHandle : Nat) : Traceful (CommunicationMessage α) := do
  let receiverSecretKey ← LongTermKeys.getPrivateKey (pkeKeyName α)
    receiver handles.ownPkeSecretKey
  let encryptedMessage ← Network.receiveMessage messageHandle
  let message ← decryptMessage receiverSecretKey encryptedMessage
  guard (message.receiver = receiver)
  ProtocolEvent.logEvent
    (.confidentialReceive message.sender receiver message.payload : CoreEvent α)
  pure message

@[expose] public def signMessage
    (sender receiver : Participant)
    (input : Sum α (Bytes × Bytes))
    (senderSecretKey nonce : Bytes) : Bytes :=
  let signatureInput : SignatureInput α := match input with
    | .inl payload => .plain sender receiver payload
    | .inr (payload, receiverPublicKey) => .encrypted payload receiverPublicKey
  let message := serialize signatureInput
  let signature := Signature.sign senderSecretKey nonce message
  serialize (.signature { message, signature } : WireMessage α)

@[expose] public def getSender
    (signedMessage : Bytes) (receiverSecretKey : Option Bytes) : Err Participant := do
  let wire : WireMessage α ← parse signedMessage
  let signed ← match wire with
    | .signature message => pure message
    | _ => failure
  let input : SignatureInput α ← parse signed.message
  match input, receiverSecretKey with
  | .plain sender _ _, none => pure sender
  | .encrypted payload _, some secretKey => do
    let plaintext ← PublicKeyEncryption.decrypt secretKey payload
    let encryptedInput : EncryptionInput α ← parse plaintext
    match encryptedInput with
    | .signed sender _ _ => pure sender
    | .unsigned .. => failure
  | _, _ => failure

@[expose] public def verifyMessage
    (sender receiver : Participant)
    (signedMessage : Bytes)
    (receiverSecretKey : Option Bytes)
    (senderVerificationKey : Bytes) : Err (Sum α Bytes) := do
  let wire : WireMessage α ← parse signedMessage
  let signed ← match wire with
    | .signature message => pure message
    | _ => failure
  let input : SignatureInput α ← parse signed.message
  guard (Signature.verify senderVerificationKey signed.message signed.signature)
  match input, receiverSecretKey with
  | .plain actualSender actualReceiver payload, none => do
    guard (actualSender = sender)
    guard (actualReceiver = receiver)
    pure (.inl payload)
  | .encrypted encryptedPayload receiverPublicKey, some secretKey => do
    guard (receiverPublicKey = PublicKeyEncryption.pk secretKey)
    let plaintext ← PublicKeyEncryption.decrypt secretKey encryptedPayload
    let encryptedInput : EncryptionInput α ← parse plaintext
    match encryptedInput with
    | .signed actualSender actualReceiver _ => do
      guard (actualSender = sender)
      guard (actualReceiver = receiver)
      pure (.inr encryptedPayload)
    | .unsigned .. => failure
  | _, _ => failure

public def sendAuthenticated
    (handles : CommunicationKeyHandles)
    (sender receiver : Participant) (payload : α) : Traceful Nat := do
  let senderSecretKey ← LongTermKeys.getPrivateKey (signatureKeyName α)
    sender handles.ownSignatureSecretKey
  let nonce ← Random.genRand 32
  ProtocolEvent.logEvent (.authenticatedSend sender receiver payload : CoreEvent α)
  Network.sendMessage (signMessage sender receiver (.inl payload) senderSecretKey nonce)

public def receiveAuthenticated
    (handles : CommunicationKeyHandles)
    (receiver : Participant) (messageHandle : Nat) : Traceful (CommunicationMessage α) := do
  let signedMessage ← Network.receiveMessage messageHandle
  let sender ← getSender (α := α) signedMessage none
  let senderVerificationKey ← LongTermKeys.getPublicKey (signatureKeyName α)
    sender handles.peerSignaturePublicKey
  let verified : Sum α Bytes ← verifyMessage (α := α) sender receiver signedMessage none
    senderVerificationKey
  let payload ← match verified with
    | .inl payload => pure payload
    | .inr _ => failure
  ProtocolEvent.logEvent (.authenticatedReceive sender receiver payload : CoreEvent α)
  pure { sender, receiver, payload }

@[expose] public def encryptAndSignMessage
    (sender receiver : Participant) (payload : α)
    (receiverPublicKey senderSecretKey encryptionNonce signatureNonce : Bytes) : Bytes :=
  let encryptedPayload := PublicKeyEncryption.encrypt receiverPublicKey encryptionNonce <|
    serialize (.signed sender receiver payload : EncryptionInput α)
  signMessage (α := α) sender receiver (.inr (encryptedPayload, receiverPublicKey))
    senderSecretKey signatureNonce

public def sendConfidentialAuthenticated
    (handles : CommunicationKeyHandles)
    (sender receiver : Participant) (payload : α) : Traceful Nat := do
  let receiverPublicKey ← LongTermKeys.getPublicKey (pkeKeyName α)
    receiver handles.peerPkePublicKey
  let senderSecretKey ← LongTermKeys.getPrivateKey (signatureKeyName α)
    sender handles.ownSignatureSecretKey
  let encryptionNonce ← Random.genRand 32
  let signatureNonce ← Random.genRand 32
  ProtocolEvent.logEvent
    (.confidentialAuthenticatedSend sender receiver payload : CoreEvent α)
  Network.sendMessage <| encryptAndSignMessage sender receiver payload receiverPublicKey
    senderSecretKey encryptionNonce signatureNonce

@[expose] public def verifyAndDecryptMessage
    (sender receiver : Participant)
    (receiverSecretKey senderVerificationKey encryptedSignedMessage : Bytes) :
    Err (CommunicationMessage α) := do
  let verified : Sum α Bytes ← verifyMessage (α := α) sender receiver encryptedSignedMessage
    (some receiverSecretKey) senderVerificationKey
  let encryptedPayload : Bytes ← match verified with
    | .inr payload => pure payload
    | .inl _ => failure
  let plaintext ← PublicKeyEncryption.decrypt receiverSecretKey encryptedPayload
  let input : EncryptionInput α ← parse plaintext
  match input with
  | .signed actualSender actualReceiver payload => do
    guard (actualSender = sender)
    guard (actualReceiver = receiver)
    pure { sender, receiver, payload }
  | .unsigned .. => failure

public def receiveConfidentialAuthenticated
    (handles : CommunicationKeyHandles)
    (receiver : Participant) (messageHandle : Nat) : Traceful (CommunicationMessage α) := do
  let encryptedSignedMessage ← Network.receiveMessage messageHandle
  let receiverSecretKey ← LongTermKeys.getPrivateKey (pkeKeyName α)
    receiver handles.ownPkeSecretKey
  let sender ← getSender (α := α) encryptedSignedMessage (some receiverSecretKey)
  let senderVerificationKey ← LongTermKeys.getPublicKey (signatureKeyName α)
    sender handles.peerSignaturePublicKey
  let message ← verifyAndDecryptMessage (α := α) sender receiver receiverSecretKey
    senderVerificationKey encryptedSignedMessage
  ProtocolEvent.logEvent
    (.confidentialAuthenticatedReceive sender receiver message.payload : CoreEvent α)
  pure message

public def initializeCore (sender receiver : Participant) :
    Traceful (CommunicationKeyHandles × CommunicationKeyHandles) := do
  let (_, senderPkePublic, senderPkeSecret) ←
    LongTermKeys.generateKeyPair (pkeKeyName α) sender
  let (_, receiverPkePublic, receiverPkeSecret) ←
    LongTermKeys.generateKeyPair (pkeKeyName α) receiver
  let (_, senderSignaturePublic, senderSignatureSecret) ←
    LongTermKeys.generateKeyPair (signatureKeyName α) sender
  let (_, receiverSignaturePublic, receiverSignatureSecret) ←
    LongTermKeys.generateKeyPair (signatureKeyName α) receiver
  pure (
    {
      ownPkeSecretKey := senderPkeSecret
      peerPkePublicKey := receiverPkePublic
      ownSignatureSecretKey := senderSignatureSecret
      peerSignaturePublicKey := receiverSignaturePublic
    },
    {
      ownPkeSecretKey := receiverPkeSecret
      peerPkePublicKey := senderPkePublic
      ownSignatureSecretKey := receiverSignatureSecret
      peerSignaturePublicKey := senderSignaturePublic
    })

end Runtime

end DY.Communication
