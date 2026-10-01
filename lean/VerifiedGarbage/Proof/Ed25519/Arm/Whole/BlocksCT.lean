import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem step_sp_ct {i : Instr} {is : List Instr}
    (ha : ∀ a b : State, a.sp = b.sp → addrs i a = addrs i b)
    (ht : RelCT isa (fun a b => a.sp = b.sp) (.block is) (fun a b => a.sp = b.sp)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (i::is)) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (ht := ht)
  intro a b a' b' hp ea eb
  exact ⟨ha a b hp,(exec_sp ea).trans (hp.trans (exec_sp eb).symm)⟩

theorem setArg_ct (r : Reg) (v : Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setArg r v)) (fun a b => a.sp = b.sp) := by
  cases v with
  | const n => exact step_sp_ct (fun _ _ _ => rfl) block_nil_ct
  | frame d => exact step_sp_ct (fun _ _ _ => rfl) block_nil_ct
  | caller j d =>
    exact step_sp_ct (fun _ _ h => by simp only [addrs,h])
      (step_sp_ct (fun _ _ _ => rfl) block_nil_ct)

theorem addSp_store_ct (j : Nat) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 (4*j),.str .r0 .r12 0]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    by_cases h : 4*j < 256
    · simp only [exec,h,ite_true,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 (4*j)) hp⟩
    · simp only [exec,h,ite_false,reduceCtorEq] at ha
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem putArg_ct (j : Nat) (v : Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (putArg j v)) (fun a b => a.sp = b.sp) :=
  block_append_ct (setArg_ct _ _) (addSp_store_ct _)

theorem setupStack_ct (start : Nat) (vs : List Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setupStack start vs)) (fun a b => a.sp = b.sp) := by
  induction vs generalizing start with
  | nil => exact block_nil_ct
  | cons v vs ih => exact block_append_ct (putArg_ct _ _) (ih _)

theorem setupRegs_ct (args : List (Reg × Value)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (args.flatMap fun (r,v) => setArg r v))
      (fun a b => a.sp = b.sp) := by
  induction args with
  | nil => exact block_nil_ct
  | cons p ps ih => exact block_append_ct (setArg_ct _ _) ih

theorem setup_ct (args : List (Reg × Value)) (stack : List Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setup args stack)) (fun a b => a.sp = b.sp) :=
  block_append_ct (setupStack_ct _ _) (setupRegs_ct _)

theorem flatMap_sp_ct {α : Type} (xs : List α) (f : α → List Instr)
    (hf : ∀ x ∈ xs, RelCT isa (fun a b => a.sp = b.sp) (.block (f x)) (fun a b => a.sp = b.sp)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (xs.flatMap f)) (fun a b => a.sp = b.sp) := by
  induction xs with
  | nil => exact block_nil_ct
  | cons x xs ih =>
    exact block_append_ct (hf x List.mem_cons_self) (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)))

theorem quiet_block_ct (is : List Instr)
    (h : ∀ i ∈ is, ∀ s, addrs i s = []) :
    RelCT isa (fun a b => a.sp = b.sp) (.block is) (fun a b => a.sp = b.sp) := by
  induction is with
  | nil => exact block_nil_ct
  | cons i is ih =>
    exact step_sp_ct (fun a b _ => (h i List.mem_cons_self a).trans (h i List.mem_cons_self b).symm)
      (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

theorem frame_store_ct (d off : Nat) (r : Reg) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 d,.str r .r12 off]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    by_cases h : d < 256
    · simp only [exec,h,ite_true,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 d) hp⟩
    · simp only [exec,h,ite_false,reduceCtorEq] at ha
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem zeroWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (zeroWord k)) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    simp only [exec,show 0 < 256 from by decide,ite_true,Option.some.injEq] at ha hb
    subst a' b'
    exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 0) hp⟩
  · apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
    · intro a b a' b' hp ha hb
      simp only [exec,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp.1,by simpa only [RegUpd.gpr_setReg,reduceCtorEq,ite_false] using hp.2⟩
    · apply block_cons_ct (ht := block_nil_ct)
      intro a b a' b' hp ha hb
      exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem zeroWords_ct (start count : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (zeroWords start count)) (fun a b => a.sp = b.sp) :=
  flatMap_sp_ct _ _ (fun _ _ => zeroWord_ct _)

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1,hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.Arm.Whole
