import VerifiedGarbage.Proof.Argon2.X86.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.X86.HPrime.FinishCT
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 H′ on x86 (32-bit): verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the arguments,
`first` and `finishOutput` by their pieces; then `hPrime_verified` against the
contract with the arguments read only, and `hPrimeShared_verified` against
`Spec.Argon2.hPrimeContract`, which lets the code write them.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm wp_cmpi contains_addr)

/-! ## The setup -/

/-- The taint analysis of the setup starts with the stack arguments public,
and the word holding `scratch` known to be the base of the second writable
region. -/
def τS : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16384], argLen := 24, argBases := [(20, 1)] }

theorem wfS {s : State} (hp : Pre s) : VG.X86.Taint.Wf τS s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_hi
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τS], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τS, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agreeS {s₁ s₂ : State} (hp₁ : Pre s₁) (hp₂ : Pre s₂) (q : Same s₁ s₂) :
    VG.X86.Taint.Agree τS s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfS hp₁, wfS hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => q.esp.symm,
    fun k h4 hk => ?_⟩
  · simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact q.esp.symm
  · rw [hp₁.wr, hp₂.wr]
    simp only [outR, scrR, P, op, ol, scr, q.args 2 (by decide), q.args 3 (by decide),
      q.args 4 (by decide)]
  · simp only [τS] at hk
    rw [show VG.X86.Taint.depth τS.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_hi; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_hi; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (q.args _ (by omega)).symm

theorem setup_F0 {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (F0 s₀) := by
  have hif := hp.in_fits
  refine (setup_ok hp).mono fun t ⟨b, o, e, f⟩ => ⟨b, o, e, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi

theorem setup_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) τS (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact setup_F0 hp, by subst e₂; exact setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Sha512.X86.at_ .ebx leftOff)), .alu .cmp .edx (.imm 65)]) s
      fun t => t.cf = some (decide (ol s₀ < 65)) := by
  have hs := hp.scr_fits
  have hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  refine wp_movm (VG.Proof.Sha512.X86.ea_of h.body.ebx leftOff)
    (by rw [h.body.rd, h.body.wr]
        exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩) fun s₁ u₁ =>
    wp_cmpi fun s₂ _ cf₂ _ => WP.block_nil ?_
  rw [cf₂, u₁.gpr, h.out.left, List.length_nil, Nat.sub_zero,
    Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (rel_taint [.ebx] (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.body.ebx, h₂.body.ebx, q.scr_eq]) ⟨_, by taint_decide⟩
    (fun _ h => choose_blk hp h) (fun _ h => choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨f₁, f₂⟩ => by show t₁.cf = t₂.cf; rw [f₁, f₂, q.ol_eq])
    (RelCT.nil fun _ _ _ => trivial)
    (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => nomatch h) (by taint_decide))

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun t₁ t₂ =>
      (F0 s₀ t₁ ∧ (digest s₀ t₁).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) ∧
      (F0 s₀' t₂ ∧ (digest s₀' t₂).take (nF s₀') =
        Spec.Argon2.H (nF s₀') (Spec.Argon2.le32 (ol s₀') ++ inB s₀')) := by
  have hs := hp.scr_fits
  have hif := hp.in_fits
  have nE : nF s₀' = nF s₀ := by simp only [nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (choose_rel hp hp' q) (fun _ h => first_choose hp h)
    (fun _ h => first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((init_rel (B := scr s₀) (E := esp₀ s₀) (n := nF s₀) (nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr_eq, q.esp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => first_init hp h) (fun _ h => first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((absorbFixed_rel (B := scr s₀) (E := esp₀ s₀) (offset := 832) (size := 4)
      (by omega) (by decide) (by decide) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
      fixed_check_832).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := pfx_cov hp' f₂.body
          simp only [P] at v
          rw [q.scr_eq, q.esp] at c; rw [q.scr_eq] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => first_fixed hp h) (fun _ h => first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => first_input hp h) (fun _ h => first_input hp' h))
    (rel_wp ?_ (fun _ h => first_finish hp h) (fun _ h => first_finish hp' h))
  · unfold absorbInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (absorbInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (absorbInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact update_rel hif (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (rel_taint [.esp, .ebx] (fun _ _ h₁ h₂ => agree_body q h₁.1.body h₂.1.body)
      ⟨_, by taint_decide⟩ (fun _ h => (finishInput_blk hp h.1).mono fun _ h => h.1)
      (fun _ h => (finishInput_blk hp' h.1).mono fun _ h => by
        have h := h.1
        rw [q.scr_eq, q.esp, cntLo, cntHi, q.inl_eq] at h; exact h)) ?_
    exact finalize_rel

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeX86.pre hPrimeX86.pub Impl.Argon2.X86.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := pre_of s₀ h₀
  have hp' := pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.X86.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.X86.HPrime.code
  refine RelCT.seq (setup_rel hp hp' q) (RelCT.seq (first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => Body s₀ t₁ ∧ Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out, f₁.ebp⟩, ⟨f₂.body, f₂.out, f₂.ebp⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (τr [.ebx]) (fun _ _ ⟨b₁, b₂⟩ => agree_regs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.ebx, b₂.ebx, q.scr_eq]) (by taint_decide)


/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x10000` at `0x5004`. -/
def hSatMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5016 then 1 else 0

def hSatState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := hSatMem
  rd := [⟨0x1000, 1⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeX86.pre hSatState := by
  have a0 : arg hSatState 0 = 0x1000 := by decide
  have a1 : arg hSatState 1 = 1 := by decide
  have a2 : arg hSatState 2 = 0x2000 := by decide
  have a3 : arg hSatState 3 = 1 := by decide
  have a4 : arg hSatState 4 = 0x10000 := by decide
  have e : argAddr hSatState 0 = 0x5004 := by decide
  simp only [hPrimeX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified X86.target Impl.Argon2.X86.HPrime.code hPrimeX86 :=
  ⟨fun s hs => correct (pre_of s hs), code_ct, ⟨hSatState, hSat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `hPrimeX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def hPrimeWide : Contract X86.isa :=
  { hPrimeX86 with
    pre := fun s =>
      let input : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let out : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 16384⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩
      s.rd = [input] ∧ s.wr = [out, scratch, args] ∧
      input.Disjoint out ∧ input.Disjoint scratch ∧ input.Disjoint args ∧ out.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      ret.Disjoint input ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
      stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧ stack.Disjoint args ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 16384 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 20 ≤ 2 ^ 32 ∧
      (arg s 1).toNat < 2 ^ 32 ∧ 1 ≤ (arg s 3).toNat ∧ (arg s 3).toNat < 2 ^ 32 }

/-- A state satisfying `hPrimeWide.pre`. -/
def hSatWide : State :=
  { hSatState with rd := [⟨0x1000, 1⟩], wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩, ⟨0x5004, 20⟩] }

macro "hnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [hPrimeX86, hPrimeWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem hPrimeWide_verified : Verified X86.target Impl.Argon2.X86.HPrime.code hPrimeWide :=
  Verified.narrowTo hPrime_verified
    (fun s => [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 20⟩])
    (fun s => [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨(arg s 4).setWidth 64, 16384⟩])
    (fun s h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
        h₂₁, h₂₂, h₂₃, h₂₄⟩ := h
      have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 60).setWidth 64, 60⟩ : Region) =
          ⟨(s.gpr .esp).setWidth 64 - 60, 60⟩ := by rw [Taint.sub_setWidth h₂₀]; rfl
      hnarrow
      refine ⟨trivial, trivial, h₄, h₆, h₇.symm, h₈.symm, h₁₀, h₁₁, ?_, ?_, ?_, h₁₇, h₁₈, h₁₉, h₂₀,
        by omega, h₂₃⟩
      · simp only [below]; rw [e]; exact h₁₃
      · simp only [below]; rw [e]; exact h₁₄
      · simp only [below]; rw [e]; exact h₁₅)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by hnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by hnarrow; exact h)
    ⟨hSatWide, by
      have a0 : arg hSatWide 0 = 0x1000 := by decide
      have a1 : arg hSatWide 1 = 1 := by decide
      have a2 : arg hSatWide 2 = 0x2000 := by decide
      have a3 : arg hSatWide 3 = 1 := by decide
      have a4 : arg hSatWide 4 = 0x10000 := by decide
      have e : argAddr hSatWide 0 = 0x5004 := by decide
      simp only [hPrimeWide, a0, a1, a2, a3, a4, e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem hPrime_implies : hPrimeWide.Implies (Spec.Argon2.hPrimeContract X86.abi 60) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, hPrimeWide, hPrimeX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [hSatWide, hSatState, hSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using hSatWide

/-- The emitted function, against the shared contract. -/
theorem hPrimeShared_verified :
    Verified X86.target Impl.Argon2.X86.HPrime.code (Spec.Argon2.hPrimeContract X86.abi 60) :=
  hPrimeWide_verified.of_implies hPrime_implies

end VG.Proof.Argon2.X86.HPrime
