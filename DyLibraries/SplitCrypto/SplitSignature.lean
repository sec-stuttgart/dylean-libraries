module

public import DY.EquationalTheory.Sign

/-! Usage-based composition of Signature predicates and their proofs.
The primitive API and byte invariants remain in `Sign.lean`.
-/

namespace DY.Signature

variable [ExecTraceTypes] [ProofTraceTypes] [BytesFunctor]

/-- DY* crypto splitting: select a local predicate by its key-usage tag.
The distinctness proof excludes ambiguous registrations. Unknown tags and wrong
usage kinds are rejected; the complete usage is passed to the local predicate. -/
@[expose, instance_reducible]
public def SignPred.combine
  {ι : Type} (components : ι → String × SignPred)
  (_distinct : Function.Injective (fun i => (components i).1)) :
  SignPred
where
  pred usage verificationKey message tr :=
    usage.type = "SigKey" ∧ ∃ i, usage.tag = (components i).1 ∧
      (components i).2.pred usage verificationKey message tr

/-- Agreement with a local crypto predicate at its registered usage tag. -/
public class SignPred.HasStep
  (tag : String) (component combined : SignPred) : Prop where
  pred_eq : ∀ [BytesWellFormed] [GetUsage] [GetLabel] usage verificationKey message tr,
    usage.type = "SigKey" → usage.tag = tag →
    (combined.pred usage verificationKey message tr ↔ component.pred usage verificationKey message tr)

/-- The global crypto predicate agrees with a local predicate on its tag. -/
public class SignPred.Has [combined : SignPred]
  (tag : String) (component : SignPred) : Prop extends SignPred.HasStep tag component combined

public instance (tag : String) (component : SignPred) :
  @SignPred.Has _ _ _ component tag component where
  pred_eq := by intros; rfl

/-- Distinct registrations give bidirectional local/global predicate agreement. -/
public theorem SignPred.hasStep_combine
  {ι : Type} (components : ι → String × SignPred)
  (distinct : Function.Injective (fun i => (components i).1)) (i : ι) :
  SignPred.HasStep (components i).1 (components i).2 (SignPred.combine components distinct)
where
  pred_eq := by
    intro _ _ _ usage verificationKey message tr ht hg
    constructor
    · rintro ⟨_, j, hj, hp⟩
      have : j = i := distinct (hj.symm.trans hg)
      subst j
      exact hp
    · intro hp
      exact ⟨ht, i, hg, hp⟩

/-- Transport local agreement through an intermediate combined policy. -/
public theorem SignPred.Has.of_hasStep
  (tag : String) (component combined : SignPred) [global : SignPred]
  [step : SignPred.HasStep tag component combined] [outer : @SignPred.Has _ _ _ global tag combined] :
  @SignPred.Has _ _ _ global tag component
where
  pred_eq := by
    intro _ _ _ usage verificationKey message tr ht hg
    exact (outer.pred_eq usage verificationKey message tr ht hg).trans (step.pred_eq usage verificationKey message tr ht hg)

/-- Local proof obligations establish the combined predicate's obligations. -/
public theorem SignPredProof.combine
  [BytesInvariants]
  {ι : Type} (components : ι → String × SignPred)
  (distinct : Function.Injective (fun i => (components i).1))
  (proofs : ∀ i, letI := (components i).2; SignPredProof) :
  letI := SignPred.combine components distinct; SignPredProof
:= by
  letI := SignPred.combine components distinct
  refine { pred_later := ?_ }
  · intro _ _ _ usage verificationKey message tr1 tr2 hk hm hle h
    obtain ⟨ht, i, hg, hp⟩ := h
    exact ⟨ht, i, hg, (proofs i).pred_later usage verificationKey message tr1 tr2 hk hm hle hp⟩

end DY.Signature

namespace DY.Meta.CombineMacro

/-! Usage-based Signature predicate composition, ported from DY.Lib.Crypto.Signature.Split.
Each source exports `signTag : String`, `signPred : SignPred`, and
`signPredProof`. Use `#combine +toplevel into Signature.SignPred,
Signature.SignPredProof [BytesInvariants] from First, Second`, adding any
component proof assumptions to the proof target's binders. Without `+toplevel`,
the generated definitions are reusable and do not install a global predicate.
Tags must be computationally distinct for the generated kernel proof. Symbolic
registrations can use `combine` and `hasStep_combine` with an explicit proof.
-/

macro_rules
  | `(command| #combine_one $options* Signature.SignPred $params* from $sources,*) => do
    let options := parseOptions options
    let base := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes]))]
    let params := if options.toplevel then params else base ++ params
    let args := params.flatMap explicitNameOfBracketedBinder
    let sources := sources.getElems
    if sources.isEmpty then Lean.Macro.throwError "crypto combination requires at least one component"
    let mut arms := #[]
    for i in [:sources.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources[i]! | Lean.Macro.throwError "invalid crypto component"
      let tag := Lean.mkIdent (source.getId ++ `signTag)
      let pred := Lean.mkIdent (source.getId ++ `signPred)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(Lean.quote i) => ($tag $sourceArgs*, $pred $sourceArgs*)))
    let components := Lean.mkIdent `signPredComponents
    let distinct := Lean.mkIdent `signPredTagsDistinct
    let pred := Lean.mkIdent `signPred
    let n : Lean.TSyntax `term := Lean.quote sources.size
    let mut cmds := #[
      (← `(command| @[expose] public def $components $params* : Fin $n → String × DY.Signature.SignPred := fun $arms:matchAlt*)),
      (← `(command| public theorem $distinct $params* : Function.Injective (fun i => ($components $args* i).1) := by first | exact fun _ _ _ => Subsingleton.elim _ _ | (unfold Function.Injective; exact of_decide_eq_true rfl))),
      (← `(command| @[expose, instance_reducible] public def $pred $params* : DY.Signature.SignPred := DY.Signature.SignPred.combine ($components $args*) ($distinct $args*)))
    ]
    for i in [:sources.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources[i]! | Lean.Macro.throwError "invalid crypto component"
      let tag := Lean.mkIdent (source.getId ++ `signTag)
      let localPred := Lean.mkIdent (source.getId ++ `signPred)
      let inst ← Lean.withFreshMacroScope `(declId| inst)
      cmds := cmds.push (← `(command| public instance (priority := default) $inst $params* : DY.Signature.SignPred.HasStep ($tag $sourceArgs*) ($localPred $sourceArgs*) ($pred $args*) := DY.Signature.SignPred.hasStep_combine ($components $args*) ($distinct $args*) $(Lean.quote i)))
      let hasInst ← Lean.withFreshMacroScope `(declId| hasInst)
      cmds := cmds.push (← `(command| public instance (priority := default) $hasInst $params* [DY.Signature.SignPred] [DY.Signature.SignPred.Has ($tag $sourceArgs*) ($pred $args*)] : DY.Signature.SignPred.Has ($tag $sourceArgs*) ($localPred $sourceArgs*) := DY.Signature.SignPred.Has.of_hasStep ($tag $sourceArgs*) ($localPred $sourceArgs*) ($pred $args*)))
    if options.toplevel then
      let inst ← Lean.withFreshMacroScope `(declId| inst)
      cmds := cmds.push (← `(command| public instance (priority := default) $inst $params* : DY.Signature.SignPred := $pred $args*))
    return Lean.mkNullNode cmds

macro_rules
  | `(command| #combine_one $options* Signature.SignPredProof $params* from $sources,*) => do
    let options := parseOptions options
    let base := #[(← `(bracketedBinder| [DY.BytesFunctor])), (← `(bracketedBinder| [DY.ExecTraceTypes])), (← `(bracketedBinder| [DY.ProofTraceTypes])), (← `(bracketedBinder| [DY.BytesInvariants]))]
    let params := if options.toplevel then params else base ++ params
    let args := params.flatMap explicitNameOfBracketedBinder
    let mut arms := #[]
    for i in [:sources.getElems.size] do
      let `(combine_from| $source:ident $sourceArgs*) := sources.getElems[i]! | Lean.Macro.throwError "invalid crypto component"
      let proof := Lean.mkIdent (source.getId ++ `signPredProof)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(Lean.quote i) => $proof $sourceArgs*))
    let components := Lean.mkIdent `signPredComponents
    let distinct := Lean.mkIdent `signPredTagsDistinct
    let pred := Lean.mkIdent `signPred
    let proof := Lean.mkIdent `signPredProof
    let combined ← `(command| public theorem $proof $params* : letI := $pred $args*; DY.Signature.SignPredProof := DY.Signature.SignPredProof.combine ($components $args*) ($distinct $args*) (fun $arms:matchAlt*))
    let inst ← Lean.withFreshMacroScope `(declId| inst)
    let top ← `(command| public instance (priority := default) $inst $params* : DY.Signature.SignPredProof := $proof $args*)
    return Lean.mkNullNode (#[combined] ++ if options.toplevel then #[top] else #[])

end DY.Meta.CombineMacro
