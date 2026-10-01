import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

/-! Reusable verified SHA-512 calls within the complete-operation frame. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86
open VG.Impl.Sha512.X86.Stream

abbrev slots (E : BitVec 32) (t : State) (j : Nat) : BitVec 32 :=
  t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32

theorem call_arg {E : BitVec 32} {t : State} (he : t.gpr .esp = E)
    (hE : 24 ≤ E.toNat) (hF : E.toNat + 256 ≤ 2 ^ 32) {j : Nat} (hj : j < 64) :
    arg t.callEntry j = slots E t j := by
  rw [arg_callEntry (by rw [he]; omega) (by rw [he]; omega), he]
  change t.mem.readW (addr E (4 * j)) 32 = slots E t j
  rw [addr_eq (x := E) (k := 4 * j) (by omega)]

theorem callEntry_frame (t : State) : Frame [below (t.gpr .esp) 4] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem]
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem callEntry_bytes {t : State} {r : Region}
    (hd : r.Disjoint (below (t.gpr .esp) 4)) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt t.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact Frame.bytes (callEntry_frame t) (by simpa only [List.mem_singleton] using fun R (h : R = below (t.gpr .esp) 4) => h ▸ hd)
    hn (List.mem_range.mp hi)

theorem callEntry_repr {t : State} {p : Addr} {iv : Spec.Sha512.HashValue} {m : List Byte}
    (hd : Region.Disjoint ⟨p, 192⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr iv t.mem p m) : Spec.Sha512.Repr iv t.callEntry.mem p m := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hr
  intro i hi
  exact Frame.bytes (R := ⟨p, 192⟩) (callEntry_frame t)
    (by intro R h; simp only [List.mem_singleton] at h; subst h; exact hd)
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem init_nosp : NoSp (init Spec.Sha512.H0_512) := NoSp.of_all (by decide +kernel)
theorem init_stack : stackUse (init Spec.Sha512.H0_512) = 0 := rfl
theorem update_nosp : NoSp update := NoSp.of_all (by lit_decide)
theorem update_stack : stackUse update = 20 := by lit_decide
theorem finalize_nosp : NoSp finalize := NoSp.of_all (by lit_decide)
theorem finalize_stack : stackUse finalize = 20 := by lit_decide

variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region} {t : State}

/-- Initialize SHA-512 while retaining the shared frame context. -/
theorem init_call (hc : Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initX86 Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr : BitVec 32} (ha : arg t.callEntry 0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (init Spec.Sha512.H0_512)) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (scr.setWidth 64) [] := by
  refine call_ok hc hE (Proof.Sha512.X86.Stream.init_verified _).1 init_nosp
    (by rw [init_stack]; decide) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  change Spec.Sha512.Repr Spec.Sha512.H0_512 s₂.mem ((arg t.callEntry 0).setWidth 64) [] at hpost
  rw [hm, ha] at hpost
  exact hpost

/-- Append an arbitrary byte string; the count is the full 64-bit cdecl pair. -/
theorem update_call (hc : Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region} (hp : Proof.Sha512.updateX86.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr p len : BitVec 32} {prev : List Byte}
    (h0 : arg t.callEntry 0 = scr) (h3 : arg t.callEntry 3 = p) (h4 : arg t.callEntry 4 = len)
    (hcount : Proof.Sha512.countX86 t.callEntry = BitVec.ofNat 64 prev.length)
    (hs : Region.Disjoint ⟨scr.setWidth 64, 192⟩ (below (t.gpr .esp) 4))
    (hd : Region.Disjoint ⟨p.setWidth 64, len.toNat⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (scr.setWidth 64) prev) :
    WP isa (.call Spec.Sha512.updateApi.name update) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt t.mem (p.setWidth 64) len.toNat) := by
  refine call_ok hc hE Proof.Sha512.X86.Stream.Update.update_verified.1 update_nosp
    (by rw [update_stack]) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  have h := hpost Spec.Sha512.H0_512 prev
    (by change Spec.Sha512.Repr _ t.callEntry.mem _ _; rw [arg_withRegions, h0]; exact callEntry_repr hs hr) hcount
  change Spec.Sha512.Repr _ s₂.mem ((arg t.callEntry 0).setWidth 64)
    (prev ++ Spec.Ed25519.bytesAt t.callEntry.mem ((arg t.callEntry 3).setWidth 64) (arg t.callEntry 4).toNat) at h
  rw [hm, h0, h3, h4, callEntry_bytes hd (by change len.toNat ≤ 2 ^ 64; have := len.isLt; omega)] at h
  exact h

/-- Finalize into any separate 64-byte buffer, including the frame's digest. -/
theorem finalize_call (hc : Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region} (hp : Proof.Sha512.finalizeX86.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr out : BitVec 32} {msg : List Byte}
    (h0 : arg t.callEntry 0 = scr) (h3 : arg t.callEntry 3 = out)
    (hcount : Proof.Sha512.countX86 t.callEntry = BitVec.ofNat 64 msg.length)
    (hs : Region.Disjoint ⟨scr.setWidth 64, 192⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (scr.setWidth 64) msg) (hlen : msg.length < 2 ^ 64) :
    WP isa (.call Spec.Sha512.finalizeApi.name finalize) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem (out.setWidth 64) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine call_ok hc hE Proof.Sha512.X86.Stream.Finalize.finalize_verified.1 finalize_nosp
    (by rw [finalize_stack]) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  have h := hpost Spec.Sha512.H0_512 msg
    (by change Spec.Sha512.Repr _ t.callEntry.mem _ _; rw [arg_withRegions, h0]; exact callEntry_repr hs hr) hlen hcount
  change Spec.Ed25519.bytesAt s₂.mem ((arg t.callEntry 3).setWidth 64) 64 = _ at h
  rw [hm, h3] at h
  exact h

end VG.Proof.Ed25519.X86.Whole
