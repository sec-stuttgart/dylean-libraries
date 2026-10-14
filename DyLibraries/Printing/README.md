# Trace printing

Build and print the Login sanity check:

```sh
lake build
.lake/build/bin/loginTrace > login-trace.jsonl
```

`lake exe loginTrace` also builds and runs the executable. The executable calls
`successfulLogin` from `Examples/Login/SanityChecks.lean`, prints its returned
execution trace, and exits with status 0 only if the run returns `some true`.
On failure it still prints the accumulated trace and reports failure on stderr.
Its stdout contains JSON lines only.

Inside `SanityChecks.lean`, use `#eval IO.print successfulLoginTrace` to inspect
the same output in the IDE.

## JSON format and DY* differences

The format follows `DY.Lib.Printing.fst`: one JSON object per line, ordered
chronologically, with zero-based `TraceID`. Strings are escaped by Lean's JSON
encoder. The string renderer always emits `TraceID` as the first field; the
remaining fields retain the JSON encoder's key order. `traceToJson` still returns
ordinary JSON objects, whose field order is not significant.

| Type | Other fields |
| --- | --- |
| `Message` | `Content` (string) |
| `Nonce` | `Usage` (null; see below) |
| `Session` | `SessionID` (number), `Principal`, `Tag`, `Content` (strings) |
| `Event` | `Principal`, `Tag`, `Content` (strings) |

This preserves DY*'s envelope and field names, with these representation-specific
differences; it does not promise compatibility with tools that require every
DY* field to have its original value type:

- `Random.ExecEntryT` contains only a length. Labels and usages are erased, so
  `Usage` is `null`, not a fabricated `NoUsage` object. As in DY*'s JSON output,
  the nonce length is not included. Symbolic bytes refer to it as `Nonce #<id>`.
- DYLean state handles are entry indices, so `SessionID` equals `TraceID`.
  States are typed values; `Tag` identifies their payload type. A global state
  without an owner uses an empty `Principal`.
- DYLean compromise entries are `ProtocolEvent` values containing the exposed
  state, not DY* `Corrupt timestamp` values. They print as `Event`, with a
  `Compromise.` tag prefix. No corruption timestamp is invented. The subsequent
  network publication is a separate `Message` entry.
- Network entries contain only bytes. Sender/receiver identities are shown in
  the corresponding communication events, not guessed for network messages.
- Literal byte rendering preserves every byte: printable ASCII is quoted,
  quotes/backslashes are escaped, and other bytes use `\xNN`. Concatenations
  remain explicit `[left,right]` terms. DY*'s renderer filters some literal
  bytes and flattens some concatenations. `Content` is still a JSON string.

No protocol actions, traces, or proof annotations are changed by printing.

## Configure a protocol

Import `DyLibraries.Printing`, or `DyLibraries.Communication.Printing` for communication payloads.
After defining the protocol's `BytesFunctor`, combine its constructor printers
with **the same source list and order**:

```lean
#combine +toplevel into BytesPrinter from Random, Literal, Concat, PublicKeyEncryption, Signature, AEAD
```

Define `Printing.PayloadPrinter` instances for protocol-specific states and
events. Each supplies a `tag`, a `render` function receiving the configured byte
renderer, and optionally a `principal` function. Local-state wrappers supply
their recorded participant automatically. Communication and long-term-key
payload instances are provided by the library.

Combine entry printers with **the same source list and order** as `ExecEntryT`:

```lean
#combine +toplevel into entryPrinter from Network, Random, ProtocolEvent MyEvent
```

Then render the returned trace:

```lean
let (_, tr) := protocol.run Trace.nil
IO.print (Printing.traceToString entryPrinter Printing.defaultPrinters tr.val)
```

See [Examples/Login/Printing.lean](../../Examples/Login/Printing.lean) for a complete configuration, including an
optional typed network-message decoder. `Printers.messageToString` returns
`Option String`: `some` overrides the symbolic rendering, while `none` falls
back to it. State/event customization uses typed instances instead of DY*'s
runtime tag registry; no serialization and reparsing is needed.

## Customize communication messages

`Communication.messageDecoder` parses bytes as a chosen type and renders the
result. Its optional final argument is a typed printer with signature
`(Bytes → String) → α → String`. The first argument to that printer renders
embedded symbolic bytes using the supplied `Printers` configuration.

```lean
messageDecoder (α := WireMessage Payload) printers bytes
messageDecoder printers bytes customWirePrinter
```

Without a custom printer, the decoder uses `PayloadPrinter.render`. Both forms
require the type's serialization and payload-printer instances, plus the usual
byte-length, literal, and concatenation instances for parsing. Parsing failure
returns `none`; `Printers.message` then falls back to `Printers.bytesToString`.

`Communication.MessagePrinters α` groups the printers for the core and
request/response layers. Every field has a default:

| Field | Printed type |
| --- | --- |
| `payload` | `α` |
| `signedMessage` | `SignedCommunicationMessage` |
| `requestMessage` | `RequestMessage α` |
| `responseEnvelope` | `ResponseEnvelope` |
| `associatedData` | `AssociatedData` |
| `wireMessage` | `WireMessage α` |
| `encryptionInput` | `EncryptionInput (WireMessage α)` |
| `signatureInput` | `SignatureInput (WireMessage α)` |

Supply only the fields you want to customize when constructing the record:

```lean
def loginMessagePrinters : MessagePrinters Payload := { payload := loginPayloadToString }
```

The default request printer uses `payload`; the default wire printer uses the
request, response, and signed-message printers. The core input printers in turn
use the wire printer. Thus a payload override propagates through the enclosing
formats. Construct a fresh record with the desired overrides: updating an
already constructed record does not rebuild the functions stored in its other
fields.

Use a field explicitly when decoding:

```lean
messageDecoder printers bytes loginMessagePrinters.wireMessage
messageDecoder printers plaintext loginMessagePrinters.encryptionInput
messageDecoder printers associatedData loginMessagePrinters.associatedData
```

These are per-call rendering choices; they do not replace global instances or
automatically change state/event rendering. Login also installs
`loginPayloadToString` as its `PayloadPrinter Payload` renderer so messages,
states, and events share the same payload presentation.

## Customize cryptographic byte constructors

The standard family printers accept optional constructor printers:

| Family printer | Optional argument type | Retained default branch |
| --- | --- | --- |
| `PublicKeyEncryption.SubF.printing` | `PartialBytesPrinter PublicKeyEncryption.Ciphertext.SubF` | Public-key construction (`Pk`) |
| `Signature.SubF.printing` | `PartialBytesPrinter Signature.Sign.SubF` | Verification-key construction (`Vk`) |
| `AEAD.SubF.printing` | `PartialBytesPrinter AEAD.Ciphertext.SubF` | No additional constructor |

Omitting the argument uses the standard symbolic printer. To customize one:

```lean
PublicKeyEncryption.SubF.printing loginPkePrinter
Signature.SubF.printing customSignaturePrinter
AEAD.SubF.printing loginAeadPrinter
```

These helpers handle the nested constructor-family dispatch. Login only needs
to assemble the outer family list, matching its `BytesFunctor` declaration:

```lean
def loginBytesPrinter : PartialBytesPrinter BytesF := Bytes.PartialFunction.combine fun
  | 0 => Random.SubF.printing
  | 1 => Literal.SubF.printing
  | 2 => Concat.SubF.printing
  | 3 => PublicKeyEncryption.SubF.printing loginPkePrinter
  | 4 => Signature.SubF.printing
  | 5 => AEAD.SubF.printing loginAeadPrinter

def loginBytesToString (b : Bytes) : String := b.rec loginBytesPrinter
```

`PartialBytesPrinter F` handles the constructors in `F`; “partial” refers to
coverage of the extensible byte datatype, not possible failure. Each constructor
printer receives a recursive callback for its child bytes. `Bytes.rec` supplies
that callback and performs the traversal, selecting a printer at every node.
The numeric indices are constructor-family tags, not trace indices.

Login's PKE printer tries to decode ciphertext plaintext as
`EncryptionInput (WireMessage Payload)`. Its AEAD printer decodes plaintext as
`Payload` and associated data as `AssociatedData`. A successful parse produces
readable `LoginRequest` or `LoginCookie` contents, preserving the cryptographic
wrapper, keys, and nonces. A failed parse falls back to recursive symbolic
printing. This recognizes the serialized format, not the origin of a ciphertext
or its validity under the protocol's invariants.

Finally, wire the custom byte renderer and network decoder together:

```lean
def loginPrinters : Printers :=
  let printers : Printers := { bytesToString := loginBytesToString }
  { printers with messageToString := fun b => messageDecoder printers b loginMessagePrinters.wireMessage }
```

The byte renderer also applies to bytes embedded in typed states and events.
Customizing only `messageToString` would leave undecoded ciphertexts using the
default symbolic rendering.

## Extend the printer

- A new byte constructor defines `SubF.printing : PartialBytesPrinter SubF`
  using the recursive callback to print child bytes. `#combine into BytesPrinter`
  composes constructor families with `Bytes.PartialFunction.combine`. All
  constructors in `DY/EquationalTheory` and `DY.Actions.Random` are covered;
  protocol-specific constructors can supply their own printers.
- A new trace component defines `entryPrinter : EntryPrinter ExecEntryT`.
  It receives the printer configuration, entry index, and typed entry, and
  returns `PrintedEntry`. `#combine into entryPrinter` handles nested unions.
- `traceToJson` exposes the JSON objects before encoding. `traceToString`
  traverses the snoc spine once and joins the rendered lines once. Neither
  needs a trace invariant, proof trace, or changes to `Traceful`.
- `PrintedEntry.toJsonString` encodes an individual entry with `TraceID` first.
  `traceToString` uses this method. Calling `.compress` on the result of
  `PrintedEntry.toJson` does not preserve that field-order guarantee.

## Validation

`lake build` builds the executable and runs the checks in
[Test.lean](Test.lean) and
[Login/SanityChecks.lean](../../Examples/Login/SanityChecks.lean). These cover
default constructor rendering, composition, JSON escaping and round trips,
`TraceID` ordering, decoder fallback, nested communication-printer overrides,
compromise entries, and successful/failed Login runs.
