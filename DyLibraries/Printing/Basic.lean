module

public import DY.Bytes.Basic
public import DY.Trace.Basic
public import Lean.Data.Json
public meta import DY.Meta.CombineMacro

namespace DY.Printing

public section

/-- A constructor printer, composed using the same recursion as byte lengths. -/
abbrev PartialBytesPrinter [BytesFunctor] (F : Type → Type) [SubBytesFunctor F] := Bytes.PartialFunction F String

def PartialBytesPrinter.combine [BytesFunctor] {n : Nat} {Fs : Fin n → Type → Type} [∀ i, SubBytesFunctor (Fs i)] (fs : (i : Fin n) → PartialBytesPrinter (Fs i)) : PartialBytesPrinter (BytesFunctor.combine Fs) := Bytes.PartialFunction.combine fs

class BytesPrinter [BytesFunctor] where
  constructors : PartialBytesPrinter BytesF

def bytesToString [BytesFunctor] [BytesPrinter] (b : Bytes) : String := b.rec BytesPrinter.constructors

/-- User decoders take precedence; a failed decoder falls back to symbolic bytes. -/
structure Printers [BytesFunctor] where
  bytesToString : Bytes → String
  messageToString : Bytes → Option String := fun _ => none

def defaultPrinters [BytesFunctor] [BytesPrinter] : Printers := ⟨bytesToString, fun _ => none⟩

def Printers.message [BytesFunctor] (p : Printers) (b : Bytes) : String :=
  match p.messageToString b with
  | some decoded => decoded
  | none => p.bytesToString b

/-- Typed contents replace DY*'s tag-indexed state and event decoders. -/
class PayloadPrinter [BytesFunctor] (α : Type) where
  tag : String
  render : (Bytes → String) → α → String
  principal : α → String := fun _ => ""

def payloadToString [BytesFunctor] [PayloadPrinter α] (p : Printers) (x : α) : String := PayloadPrinter.render p.bytesToString x

structure PrintedEntry where
  type : String
  fields : List (String × Lean.Json) := []

def PrintedEntry.toJson (e : PrintedEntry) (id : Nat) : Lean.Json := Lean.Json.mkObj (("TraceID", Lean.toJson id) :: ("Type", Lean.toJson e.type) :: e.fields)

/-- JSON objects sort their keys internally; explicitly emit TraceID first. -/
def PrintedEntry.toJsonString (e : PrintedEntry) (id : Nat) : String :=
  match e.toJson id with
  | .obj fields =>
    let (traceId, rest) := fields.toList.partition fun field => field.1 == "TraceID"
    let encoded := (traceId ++ rest).map fun (key, value) => (Lean.toJson key).compress ++ ":" ++ value.compress
    "{" ++ String.intercalate "," encoded ++ "}"
  | json => json.compress

abbrev EntryPrinter [BytesFunctor] (α : Type) := Printers → Nat → α → PrintedEntry

def EntryPrinter.combine [BytesFunctor] {n : Nat} {Ts : Fin n → Type} (ps : (i : Fin n) → EntryPrinter (Ts i)) : EntryPrinter (ExecTraceTypes.combine Ts) := fun p id e => ps e.id p id e.entry

/-- Return the array entries in chronological order. -/
def traceEntries {α : Type} (tr : Trace α) : List α := tr.toArray.toList

def traceToJson [BytesFunctor] (printer : EntryPrinter α) (p : Printers) (tr : Trace α) : List Lean.Json := (traceEntries tr).zipIdx.map fun (e, i) => (printer p i e).toJson i

/-- DY* JSON lines: one object per entry, oldest first, with a final newline. -/
def traceToString [BytesFunctor] (printer : EntryPrinter α) (p : Printers) (tr : Trace α) : String := String.join ((traceEntries tr).zipIdx.map fun (e, i) => (printer p i e).toJsonString i ++ "\n")

end
end DY.Printing

namespace DY.Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* BytesPrinter $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor]))]
    let params := if options.toplevel then params else baseParams ++ params
    let combined ← combineExplicit params sources.getElems <| .makeSimple {
      name := `SubF.printing
      refereeName := `SubF
      combineName := ``DY.Printing.PartialBytesPrinter.combine
      outTypeName := ``DY.Printing.PartialBytesPrinter
      isTheorem := false
    }
    let printer := Lean.mkIdent `SubF.printing
    let inst ← `(command| public instance : DY.Printing.BytesPrinter where constructors := $printer)
    return Lean.mkNullNode (combined ++ if options.toplevel then #[inst] else #[])
  | `(command| #combine_one $options* entryPrinter $params* from $sources,*) => do
    let options := parseOptions options
    let baseParams := #[(← `(bracketedBinder| [DY.BytesFunctor]))]
    let params := if options.toplevel then params else baseParams ++ params
    let combined ← combineExplicit params sources.getElems <| .makeSimple {
      name := `entryPrinter
      refereeName := `ExecEntryT
      combineName := ``DY.Printing.EntryPrinter.combine
      outTypeName := ``DY.Printing.EntryPrinter
      isTheorem := false
    }
    return Lean.mkNullNode combined

end DY.Meta.CombineMacro
