module

public import DyExtensions.EquationalTheory.AEAD

/-! Usage-based composition of AEAD predicates and their proofs.
The primitive API and byte invariants remain in `AEAD.lean`.
-/

namespace DY.AEAD

variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor]

/-- DY* crypto splitting: select a local predicate by its key-usage tag.
The distinctness proof excludes ambiguous registrations. Unknown tags and wrong
usage kinds are rejected; the complete usage is passed to the local predicate. -/
@[expose, instance_reducible]
public def EncryptPred.combine
  {ι : Type} (components : ι → String × EncryptPred)
  (_distinct : Function.Injective (fun i => (components i).1)) :
  EncryptPred
where
  pred usage key nonce message associatedData tr :=
    usage.type = "AeadKey" ∧ ∃ i, usage.tag = (components i).1 ∧
      (components i).2.pred usage key nonce message associatedData tr

/-- Agreement with a local crypto predicate at its registered usage tag. -/
public class EncryptPred.HasStep
  (tag : String) (component combined : EncryptPred) : Prop where
  pred_eq : ∀ [BytesWellFormed] [GetUsage] [GetLabel] usage key nonce message associatedData tr,
    usage.type = "AeadKey" → usage.tag = tag →
    (combined.pred usage key nonce message associatedData tr ↔ component.pred usage key nonce message associatedData tr)

/-- The global crypto predicate agrees with a local predicate on its tag. -/
public class EncryptPred.Has [combined : EncryptPred]
  (tag : String) (component : EncryptPred) : Prop extends EncryptPred.HasStep tag component combined

public instance (tag : String) (component : EncryptPred) :
  @EncryptPred.Has _ _ _ component tag component where
  pred_eq := by intros; rfl

/-- Distinct registrations give bidirectional local/global predicate agreement. -/
public theorem EncryptPred.hasStep_combine
  {ι : Type} (components : ι → String × EncryptPred)
  (distinct : Function.Injective (fun i => (components i).1)) (i : ι) :
  EncryptPred.HasStep (components i).1 (components i).2 (EncryptPred.combine components distinct)
where
  pred_eq := by
    intro _ _ _ usage key nonce message associatedData tr ht hg
    constructor
    · rintro ⟨_, j, hj, hp⟩
      have : j = i := distinct (hj.symm.trans hg)
      subst j
      exact hp
    · intro hp
      exact ⟨ht, i, hg, hp⟩

/-- Transport local agreement through an intermediate combined policy. -/
public theorem EncryptPred.Has.of_hasStep
  (tag : String) (component combined : EncryptPred) [global : EncryptPred]
  [step : EncryptPred.HasStep tag component combined] [outer : @EncryptPred.Has _ _ _ global tag combined] :
  @EncryptPred.Has _ _ _ global tag component
where
  pred_eq := by
    intro _ _ _ usage key nonce message associatedData tr ht hg
    exact (outer.pred_eq usage key nonce message associatedData tr ht hg).trans (step.pred_eq usage key nonce message associatedData tr ht hg)

/-- Local proof obligations establish the combined predicate's obligations. -/
public theorem EncryptPredProof.combine
  [BytesFunctor.Has AEAD.SubF] [BytesInvariants]
  {ι : Type} (components : ι → String × EncryptPred)
  (distinct : Function.Injective (fun i => (components i).1))
  (proofs : ∀ i, letI := (components i).2; EncryptPredProof) :
  letI := EncryptPred.combine components distinct; EncryptPredProof
:= by
  letI := EncryptPred.combine components distinct
  refine { pred_later := ?_, pred_key_label := ?_ }
  · intro _ _ _ usage key nonce message associatedData tr1 tr2 hk hn hm had hle h
    obtain ⟨ht, i, hg, hp⟩ := h
    exact ⟨ht, i, hg, (proofs i).pred_later usage key nonce message associatedData tr1 tr2 hk hn hm had hle hp⟩
  · intro usage key nonce message associatedData tr h
    obtain ⟨_, i, _, hp⟩ := h
    exact (proofs i).pred_key_label usage key nonce message associatedData tr hp

end DY.AEAD

namespace DY.Meta.CombineMacro

/-! Usage-based AEAD predicate composition, ported from DY.Lib.Crypto.AEAD.Split.
Each source exports `aeadTag : String`, `aeadPred : EncryptPred`, and
`aeadPredProof`. Use `#combine +toplevel into AEAD.EncryptPred,
AEAD.EncryptPredProof [BytesInvariants] from First, Second`, adding any
component proof assumptions to the proof target's binders. Without `+toplevel`,
the generated definitions are reusable and do not install a global predicate.
Tags must be computationally distinct for the generated kernel proof. Symbolic
registrations can use `combine` and `hasStep_combine` with an explicit proof.
-/

macro_rules
  | `(command| #combine_one $options* AEAD.EncryptPred $params* from $sources,*) => do
    let options := parseOptions options
    let base := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes]))]
    let params := if options.toplevel then params else base ++ params
    let args := params.flatMap explicitNameOfBracketedBinder
    let sources := sources.getElems
    if sources.isEmpty then Lean.Macro.throwError "crypto combination requires at least one component"
    let mut arms := #[]
    for i in [:sources.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources[i]! | Lean.Macro.throwError "invalid crypto component"
      let tag := Lean.mkIdent (source.getId ++ `aeadTag)
      let pred := Lean.mkIdent (source.getId ++ `aeadPred)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(Lean.quote i) => ($tag $sourceArgs*, $pred $sourceArgs*)))
    let components := Lean.mkIdent `aeadPredComponents
    let distinct := Lean.mkIdent `aeadPredTagsDistinct
    let pred := Lean.mkIdent `aeadPred
    let n : Lean.TSyntax `term := Lean.quote sources.size
    let mut cmds := #[
      (← `(command| @[expose] public def $components $params* : Fin $n → String × DY.AEAD.EncryptPred := fun $arms:matchAlt*)),
      (← `(command| public theorem $distinct $params* : Function.Injective (fun i => ($components $args* i).1) := by first | exact fun _ _ _ => Subsingleton.elim _ _ | (unfold Function.Injective; exact of_decide_eq_true rfl))),
      (← `(command| @[expose, instance_reducible] public def $pred $params* : DY.AEAD.EncryptPred := DY.AEAD.EncryptPred.combine ($components $args*) ($distinct $args*)))
    ]
    for i in [:sources.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources[i]! | Lean.Macro.throwError "invalid crypto component"
      let tag := Lean.mkIdent (source.getId ++ `aeadTag)
      let localPred := Lean.mkIdent (source.getId ++ `aeadPred)
      let inst ← Lean.withFreshMacroScope `(declId| inst)
      cmds := cmds.push (← `(command| public instance (priority := default) $inst $params* : DY.AEAD.EncryptPred.HasStep ($tag $sourceArgs*) ($localPred $sourceArgs*) ($pred $args*) := DY.AEAD.EncryptPred.hasStep_combine ($components $args*) ($distinct $args*) $(Lean.quote i)))
      let hasInst ← Lean.withFreshMacroScope `(declId| hasInst)
      cmds := cmds.push (← `(command| public instance (priority := default) $hasInst $params* [DY.AEAD.EncryptPred] [DY.AEAD.EncryptPred.Has ($tag $sourceArgs*) ($pred $args*)] : DY.AEAD.EncryptPred.Has ($tag $sourceArgs*) ($localPred $sourceArgs*) := DY.AEAD.EncryptPred.Has.of_hasStep ($tag $sourceArgs*) ($localPred $sourceArgs*) ($pred $args*)))
    if options.toplevel then
      let inst ← Lean.withFreshMacroScope `(declId| inst)
      cmds := cmds.push (← `(command| public instance (priority := default) $inst $params* : DY.AEAD.EncryptPred := $pred $args*))
    return Lean.mkNullNode cmds

macro_rules
  | `(command| #combine_one $options* AEAD.EncryptPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let base := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes])), (← `(bracketedBinder| [DY.BytesFunctor.Has DY.AEAD.SubF])), (← `(bracketedBinder| [DY.BytesInvariants]))]
    let params := if options.toplevel then params else base ++ params
    let args := params.flatMap explicitNameOfBracketedBinder
    let mut arms := #[]
    for i in [:sources.getElems.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources.getElems[i]! | Lean.Macro.throwError "invalid crypto component"
      let proof := Lean.mkIdent (source.getId ++ `aeadPredProof)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(Lean.quote i) => $proof $sourceArgs*))
    let components := Lean.mkIdent `aeadPredComponents
    let distinct := Lean.mkIdent `aeadPredTagsDistinct
    let pred := Lean.mkIdent `aeadPred
    let proof := Lean.mkIdent `aeadPredProof
    let combined ← `(command| public theorem $proof $params* : letI := $pred $args*; DY.AEAD.EncryptPredProof := DY.AEAD.EncryptPredProof.combine ($components $args*) ($distinct $args*) (fun $arms:matchAlt*))
    let inst ← Lean.withFreshMacroScope `(declId| inst)
    let top ← `(command| public instance (priority := default) $inst $params* : DY.AEAD.EncryptPredProof := $proof $args*)
    return Lean.mkNullNode (#[combined] ++ if options.toplevel then #[top] else #[])

end DY.Meta.CombineMacro
