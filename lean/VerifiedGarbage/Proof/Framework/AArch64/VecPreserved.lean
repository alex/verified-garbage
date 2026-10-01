import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! Vector register preservation, including through calls and stack frames. -/
namespace VG.AArch64

/-- Destination of an AdvSIMD instruction. -/
def VOp.dst : VOp → VReg
  | .mov d .. | .movi0 d | .dup _ d .. | .ins _ d .. | .dupS d .. => d
  | .logic _ d .. | .not d .. | .add _ d .. | .sub _ d .. | .shift _ _ d .. => d
  | .ext d .. | .rev _ d .. | .perm _ _ d .. | .tbl d .. => d
  | .umull _ d .. | .umlal _ d .. | .mul d .. | .mla d .. | .mls d .. => d
  | .sqdmulh d .. | .umin d .. | .pmull _ d .. => d
  | .aese d .. | .aesd d .. | .aesmc d .. | .aesimc d .. => d
  | .sha1 _ d .. | .sha1h d .. | .sha1su0 d .. | .sha1su1 d .. => d
  | .sha256h d .. | .sha256h2 d .. | .sha256su0 d .. | .sha256su1 d .. => d
  | .sha512h d .. | .sha512h2 d .. | .sha512su0 d .. | .sha512su1 d .. => d
  | .eor3 d .. | .bcax d .. | .rax1 d .. | .xar d .. => d

/-- The vector register an instruction writes, if any. -/
def vdstOf : Instr → Option VReg
  | .vop op => some op.dst
  | .ldrq d .. => some d
  | _ => none

theorem VOp.eval_dst {op : VOp} {s : State} {d : VReg} {v : BitVec 128}
    (h : op.eval s = some (d, v)) : d = op.dst := by
  cases op <;> (try cases ‹VArr›) <;> simp only [VOp.eval] at h
  all_goals
    repeat' split at h
    all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | exact h.1.symm | contradiction

theorem exec_vec {i : Instr} {r : VReg} {s s' : State}
    (hi : vdstOf i ≠ some r) (h : exec i s = some s') : s'.v r = s.v r := by
  cases i with
  | str sz t n off | strb t n off | strq t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | ldr sz t n off | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    rfl
  | ldrq t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    have ht : r ≠ t := fun e => hi (by simp [vdstOf, e])
    simp only [State.setV, ht, ite_false]
  | vop op =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨⟨d, v⟩, hd, rfl⟩ := h
    have ht : r ≠ d := fun e => hi (by simp [vdstOf, ← VOp.eval_dst hd, e])
    simp only [State.setV, ht, ite_false]
  | ldrSp t off =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | push _ | pop _ | alloc _ | free _ => simp only [exec, reduceCtorEq] at h
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; rfl)

theorem execBlock_vec {is : List Instr} {r : VReg} {s s' : State} {t : List Leak}
    (hc : ∀ i ∈ is, vdstOf i ≠ some r) (h : execBlock isa is s = some (s', t)) :
    s'.v r = s.v r := by
  induction is generalizing s t with
  | nil => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h2, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
        exec_vec (hc i (List.mem_cons_self ..)) he]

theorem call_vec {s s' : State} (h : isa.call s = some s') : s'.v = s.v := by
  simp only [isa, call, Option.some.injEq] at h
  subst h; rfl

theorem push_vec {i : Instr} {s s' : State} (h : isa.push i s = some s') : s'.v = s.v := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

theorem pop_vec {i : Instr} {s₁ s₂ s' : State} (h : isa.pop i s₁ s₂ = some s') :
    s'.v = s₂.v := by
  cases i <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

/-- An unwritten vector register keeps its entire value through all control flow. -/
theorem Exec.vec {c : Prog isa} {r : VReg} (hc : ∀ i ∈ instrs c, vdstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.v r = s.v r := by
  induction h with
  | block h => exact execBlock_vec hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)),
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi))]
  | iteT _ _ ih => exact ih (fun i hi => hc i (List.mem_append_left _ hi))
  | iteF _ _ ih => exact ih (fun i hi => hc i (List.mem_append_right _ hi))
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | call hc₁ _ hr ih => rw [ret_eq hr, ih hc, call_vec hc₁]
  | frame hp _ hq ih =>
    rw [pop_vec hq, ih (fun i hi => hc i (by simp [instrs, hi])), push_vec hp]

/-- Fast syntactic check: the instruction does not write a callee-saved vector. -/
def keepsV (i : Instr) : Bool :=
  match vdstOf i with
  | some .v8 | some .v9 | some .v10 | some .v11
  | some .v12 | some .v13 | some .v14 | some .v15 => false
  | _ => true

theorem keepsV_ne {i : Instr} (h : keepsV i = true) {r : VReg} (hr : r ∈ preservedV) :
    vdstOf i ≠ some r := by
  intro e
  unfold keepsV at h
  rw [e] at h
  cases r <;> simp_all [preservedV]

/-- Existing code that never writes v8–v15 preserves their low 64 bits.
The certificate checks all instructions, including callees and frames. -/
theorem Exec.preservedV {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hc : c.allInstrs keepsV = true := by decide +kernel) :
    ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  intro r hr
  rw [Exec.vec (fun i hi => keepsV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq keepsV c) ▸ hc) i hi) hr) h]

/-- Carry a low-half vector preservation fact beside any postcondition. -/
theorem WP.preservedV {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q) (hc : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.preservedV he hc⟩

/-- The GPR and stack part of the ABI, useful for intermediate proof stages.
An exported Verified proof still requires the complete ABI, including vectors. -/
def GprAbi (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

/-- Add the SIMD ABI obligation to an existing GPR/stack correctness proof. -/
theorem WP.withPreservedV {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' =>
      ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧ Q s')
    (hc : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => abiPreserved s s' ∧ Q s' := by
  obtain ⟨t, s', he, ⟨hg, hsp⟩, hq⟩ := h
  exact ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he hc⟩, hq⟩

end VG.AArch64
