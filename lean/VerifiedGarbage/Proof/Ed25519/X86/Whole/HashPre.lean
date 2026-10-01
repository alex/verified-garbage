import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash

/-! Spatial preconditions for calls of the x86 streaming SHA-512 functions. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

abbrev SHA (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 192⟩
abbrev WORK (scr : BitVec 32) : Region := ⟨(scr + 192).setWidth 64, 272⟩
abbrev ARGS (E : BitVec 32) (n : Nat) : Region := ⟨E.setWidth 64, n⟩

structure HashSpace (E scr : BitVec 32) : Prop where
  below : 24 ≤ E.toNat
  frameFit : E.toNat + 256 ≤ 2 ^ 32
  scratchFit : scr.toNat + 8192 ≤ 2 ^ 32
  sep : (STK E).Disjoint ⟨scr.setWidth 64, 8192⟩

namespace HashSpace
variable {E scr : BitVec 32} (h : HashSpace E scr)
include h

theorem work_addr : (scr + 192).setWidth 64 = scr.setWidth 64 + BitVec.ofNat 64 192 := by
  have hs := h.scratchFit
  exact addr_eq (x := scr) (k := 192) (by omega)

theorem work_fit : (scr + 192).toNat + 272 ≤ 2 ^ 32 := by
  have hs := h.scratchFit
  rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

omit h in
theorem sha_sub : Region.Sub (SHA scr) ⟨scr.setWidth 64, 8192⟩ := Region.sub_prefix (by decide)
theorem work_sub : Region.Sub (WORK scr) ⟨scr.setWidth 64, 8192⟩ := by
  rw [show WORK scr = ⟨scr.setWidth 64 + BitVec.ofNat 64 192, 272⟩ by rw [WORK, h.work_addr]]
  exact Offset.sub_base _ (by decide)

theorem sha_work : (SHA scr).Disjoint (WORK scr) := by
  change Region.Disjoint ⟨scr.setWidth 64, 192⟩ ⟨(scr + 192).setWidth 64, 272⟩
  rw [h.work_addr]
  exact Offset.base_disjoint _ (by decide) (by decide)

omit h in
theorem args_sub {n : Nat} (hn : n ≤ 256) : Region.Sub (ARGS E n) (STK E) :=
  fun p hp => frame_sub E p (Region.sub_prefix hn p hp)

theorem args_sha {n : Nat} (hn : n ≤ 256) : (ARGS E n).Disjoint (SHA scr) :=
  (h.sep.sub_left (args_sub (E := E) hn)).sub_right (HashSpace.sha_sub (scr := scr))

theorem args_work {n : Nat} (hn : n ≤ 256) : (ARGS E n).Disjoint (WORK scr) :=
  (h.sep.sub_left (args_sub (E := E) hn)).sub_right h.work_sub

theorem below_sha {n : Nat} (hn : n ≤ 24) : (VG.X86.below E n).Disjoint (SHA scr) :=
  (h.sep.sub_left (below_sub_stack h.below hn)).sub_right (HashSpace.sha_sub (scr := scr))

theorem below_work {n : Nat} (hn : n ≤ 24) : (VG.X86.below E n).Disjoint (WORK scr) :=
  (h.sep.sub_left (below_sub_stack h.below hn)).sub_right h.work_sub

theorem inner_base : (E - 4).setWidth 64 - 20 = E.setWidth 64 - 24 := by
  have he := h.below
  have e : (E - 4).setWidth 64 = E.setWidth 64 - 4 := Taint.sub_setWidth (m := 4) (by omega)
  rw [e, BitVec.sub_sub]
  rfl

theorem inner_sub : Region.Sub ⟨(E - 4).setWidth 64 - 20, 20⟩ (VG.X86.below E 24) := by
  rw [h.inner_base]
  change Region.Sub ⟨E.setWidth 64 - 24, 20⟩ ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩
  rw [Taint.sub_setWidth h.below]
  exact Region.sub_prefix (by decide)

end HashSpace

variable {E scr : BitVec 32} {t : State}

theorem arg_base (he : t.gpr .esp = E) (rd wr : List Region) :
    argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 := by
  rw [argAddr_withRegions, argAddr_callEntry, he]
  change (E + 0).setWidth 64 = E.setWidth 64
  exact congrArg (fun x : BitVec 32 => x.setWidth 64) (BitVec.add_zero E)

def initRd (E : BitVec 32) : List Region := [ARGS E 4]
def initWr (scr : BitVec 32) : List Region := [SHA scr]
def updateRd (E p len : BitVec 32) : List Region := [⟨p.setWidth 64, len.toNat⟩, ARGS E 24]
def hashWr (scr : BitVec 32) : List Region := [SHA scr, WORK scr]
def finalizeRd (E : BitVec 32) : List Region := [ARGS E 20]
def finalizeWr (scr out : BitVec 32) : List Region := [SHA scr, ⟨out.setWidth 64, 64⟩, WORK scr]

theorem init_pre (he : t.gpr .esp = E) (h : HashSpace E scr) (ha : slots E t 0 = scr) :
    (Proof.Sha512.initX86 Spec.Sha512.H0_512).pre
      (t.callEntry.withRegions (initRd E) (initWr scr)) := by
  have a0 := (call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha
  simp only [Proof.Sha512.initX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, arg_base he, he, initRd, initWr]
  have hb := h.below
  have hf := h.frameFit
  have hs := h.scratchFit
  refine ⟨trivial, trivial, h.args_sha (by decide), h.below_sha (by decide), by omega, ?_⟩
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  omega

theorem update_pre (he : t.gpr .esp = E) (h : HashSpace E scr) {p len : BitVec 32}
    (ha0 : slots E t 0 = scr) (ha3 : slots E t 3 = p) (ha4 : slots E t 4 = len)
    (ha5 : slots E t 5 = scr + 192)
    (hd : Region.Disjoint ⟨p.setWidth 64, len.toNat⟩ ⟨scr.setWidth 64, 8192⟩)
    (hb : (VG.X86.below E 24).Disjoint ⟨p.setWidth 64, len.toNat⟩)
    (hfit : p.toNat + len.toNat ≤ 2 ^ 32) :
    Proof.Sha512.updateX86.pre
      (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) := by
  have a0 := (call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha0
  have a3 := (call_arg he h.below h.frameFit (j := 3) (by decide)).trans ha3
  have a4 := (call_arg he h.below h.frameFit (j := 4) (by decide)).trans ha4
  have a5 := (call_arg he h.below h.frameFit (j := 5) (by decide)).trans ha5
  simp only [Proof.Sha512.updateX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, a3, a4, a5, arg_base he, he, updateRd, hashWr]
  have he0 := h.below
  have he1 := h.frameFit
  have hs := h.scratchFit
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  refine ⟨trivial, trivial, h.sha_work, hd.sub_right (HashSpace.sha_sub (scr := scr)), hd.sub_right h.work_sub,
    h.args_sha (by decide), h.args_work (by decide), h.below_sha (by decide), h.below_work (by decide),
    (h.below_sha (n := 24) (by decide)).sub_left h.inner_sub,
    (h.below_work (n := 24) (by decide)).sub_left h.inner_sub,
    hb.sub_left h.inner_sub, by omega, hfit, h.work_fit, ?_, ?_⟩ <;> omega

theorem finalize_pre (he : t.gpr .esp = E) (h : HashSpace E scr) {out : BitVec 32}
    (ha0 : slots E t 0 = scr) (ha3 : slots E t 3 = out) (ha4 : slots E t 4 = scr + 192)
    (hd : Region.Disjoint ⟨out.setWidth 64, 64⟩ ⟨scr.setWidth 64, 8192⟩)
    (hb : (VG.X86.below E 24).Disjoint ⟨out.setWidth 64, 64⟩)
    (ha : (ARGS E 20).Disjoint ⟨out.setWidth 64, 64⟩)
    (hfit : out.toNat + 64 ≤ 2 ^ 32) :
    Proof.Sha512.finalizeX86.pre
      (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) := by
  have a0 := (call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha0
  have a3 := (call_arg he h.below h.frameFit (j := 3) (by decide)).trans ha3
  have a4 := (call_arg he h.below h.frameFit (j := 4) (by decide)).trans ha4
  simp only [Proof.Sha512.finalizeX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, a3, a4, arg_base he, he, finalizeRd, finalizeWr]
  have he0 := h.below
  have he1 := h.frameFit
  have hs := h.scratchFit
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  refine ⟨trivial, trivial, (hd.sub_right (HashSpace.sha_sub (scr := scr))).symm, h.sha_work, hd.sub_right h.work_sub,
    h.args_sha (by decide), ha, h.args_work (by decide), h.below_sha (by decide),
    hb.sub_left (below_sub (by decide) h.below), h.below_work (by decide),
    (h.below_sha (n := 24) (by decide)).sub_left h.inner_sub, hb.sub_left h.inner_sub,
    (h.below_work (n := 24) (by decide)).sub_left h.inner_sub,
    by omega, hfit, h.work_fit, ?_, ?_⟩ <;> omega

end VG.Proof.Ed25519.X86.Whole
