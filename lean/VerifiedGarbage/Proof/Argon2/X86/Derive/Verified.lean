import VerifiedGarbage.Proof.Argon2.X86.Derive.BodyCT

/-!
# Argon2 on x86 (32-bit): the derivation is verified

`derive_verified`: the derivation against `deriveX86` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, which also lets the code write
its arguments, by narrowing (`deriveWide`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86

/-! ## A state satisfying the precondition -/

/-- The arguments: Argon2d, empty inputs, one pass over 8 KiB in one lane, a
4-byte tag. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satArgs` at `0x40004`. -/
def satMem (a : Addr) : Byte :=
  if 0x40004 ≤ a.toNat ∧ a.toNat < 0x4004C then
    ((BitVec.ofNat 32 (satArgs[(a.toNat - 0x40004) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40004) % 4))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40004, 72⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
  have e : argAddr satState 0 = 0x40004 := by decide
  have esp : satState.gpr .esp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, retR, stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, esp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
       rcases hw with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveX86 :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `deriveX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def deriveWide : Contract X86.isa :=
  { deriveX86 with
    pre := fun s =>
      let pw : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
      let salt : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let sec : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩
      let ad : Region := ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩
      let mem : Region := ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨(arg s 15).setWidth 64, 16384⟩
      let out : Region := ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩
      let args : Region := ⟨argAddr s 0, 72⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩
      s.rd = [pw, salt, sec, ad] ∧ s.wr = [mem, scr, out, args] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      ret.Disjoint mem ∧ ret.Disjoint scr ∧ ret.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32 ∧ 244 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 4 + 72 ≤ 2 ^ 32 ∧ (arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg s 8).toNat ∧ (arg s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat).blocks }

/-- A state satisfying `deriveWide.pre`. -/
def satWide : State where
  gpr := satState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩, ⟨0x40004, 72⟩]

macro "dnarrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [deriveX86, deriveWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem deriveWide_pre {s : State} (h : deriveWide.pre s) :
    DPre (s.withRegions [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩]
      [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩]) := by
  obtain ⟨_, _, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃, r₁, r₂, r₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  have e : (⟨((s.gpr .esp) - BitVec.ofNat 32 244).setWidth 64, 244⟩ : Region) =
      ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ := by rw [Taint.sub_setWidth lo]; rfl
  refine
    { rd := rfl
      wr := rfl
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      ret_w := ?_
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      esp_lo := lo
      esp_hi := (by show (s.gpr .esp).toNat + 76 ≤ 2 ^ 32; omega)
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩],
      ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], r.Disjoint w
    intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ w ∈ [(⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩ : Region), ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint w
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> with_reducible assumption
  · show ∀ r ∈ [(⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ : Region), ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
        ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩,
        ⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
        ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩], (below (s.gpr .esp) 244).Disjoint r
    rw [show below (s.gpr .esp) 244 = ⟨(s.gpr .esp).setWidth 64 - 244, 244⟩ from e]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem deriveWide_verified : Verified X86.target Impl.Argon2.X86.Derive.derive deriveWide :=
  Verified.narrowTo derive_verified
    (fun s => [⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩,
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩, ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩, ⟨argAddr s 0, 72⟩])
    (fun s => [⟨(arg s 13).setWidth 64, (arg s 14).toNat * 1024⟩, ⟨(arg s 15).setWidth 64, 16384⟩,
      ⟨(arg s 16).setWidth 64, (arg s 17).toNat⟩])
    (fun _ h => deriveWide_pre h)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
          by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ _ _ h => by dnarrow at h ⊢; exact h)
    (fun _ _ _ _ h => by dnarrow; exact h)
    ⟨satWide, by
      have a : ∀ i < 18, arg satWide i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
      have e : argAddr satWide 0 = 0x40004 := by decide
      simp only [deriveWide, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem derive_implies : deriveWide.Implies (Spec.Argon2.deriveContract X86.abi 244) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveWide, deriveX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using satWide

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified X86.target Impl.Argon2.X86.Derive.derive (Spec.Argon2.deriveContract X86.abi 244) :=
  deriveWide_verified.of_implies derive_implies

end VG.Proof.Argon2.X86.Derive
