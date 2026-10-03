import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Contract
import VerifiedGarbage.Proof.Gcm.Compose

/-!
# AES-GCM on x86: from the contracts to the pieces

Untrusted: everything here is checked by Lean. What the functions' proofs
share: the public data of a run (`pubOf`: the stack pointer and the stack
arguments), a `Pc` with no state satisfying it (`Pc.vacuous`), and facts
about the regions of the contracts.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- The public data of a run with `n` stack arguments. -/
def pubOf (n : Nat) (s : State) : BitVec 32 × (Nat → BitVec 32) :=
  (s.gpr .esp, fun i => if i < n then arg s i else 0)

theorem pubOf_eq {n : Nat} {s₁ s₂ : State} (h : pubN n s₁ s₂) : pubOf n s₁ = pubOf n s₂ := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [pubOf, h₁, Prod.mk.injEq, true_and]
  funext i
  split
  · next hi => exact h₂ i hi
  · rfl

theorem pubOf_arg {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubOf n s = p) {i : Nat}
    (hi : i < n) : arg s i = p.2 i := by
  rw [← h]; simp only [pubOf, hi, ↓reduceIte]

theorem pubOf_esp {n : Nat} {s : State} {p : BitVec 32 × (Nat → BitVec 32)} (h : pubOf n s = p) :
    s.gpr .esp = p.1 := by
  rw [← h]; rfl

/-- A piece from states none of which satisfies `P`. -/
theorem Pc.vacuous {α : Sort _} {P Q : α → State → Prop} {c : Prog isa} (h : ∀ a s, ¬ P a s) : Pc P c Q :=
  ⟨fun a s hs => absurd hs (h a s), RelCT.of_false fun _ _ ⟨⟨a, h₁⟩, _⟩ => h a _ h₁⟩

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := BitVec.eq_of_toNat_eq (by simp)

/-- The low word of a 64-bit length, modulo 16. -/
theorem lo_mod16 {hi lo : BitVec 32} {n : Nat} (h : hi ++ lo = BitVec.ofNat 64 n) : lo.toNat % 16 = n % 16 := by
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq] at e
  have hl := lo.isLt
  have e2 := congrArg (· % 2 ^ 32) e
  simp only [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt hl] at e2
  rw [e2, Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]

/-- The stack the contracts reserve, as the calls see it. -/
theorem below_eq {SP : BitVec 32} {k : Nat} (h : k ≤ SP.toNat) :
    (⟨SP.setWidth 64 - BitVec.ofNat 64 k, k⟩ : Region) = below SP k := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem ret_below {SP : BitVec 32} {k : Nat} (h : k ≤ SP.toNat) : (⟨w64 SP, 4⟩ : Region).Disjoint (below SP k) := by
  rw [← below_eq h]; exact Offset.base_disjoint_below _ (by omega)

/-- The return address stays where it is, outside a frame. -/
theorem ret_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {SP : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 SP, 4⟩ : Region).Disjoint r) : m'.readW (w64 SP) 32 = m.readW (w64 SP) 32 :=
  hf.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) hd (by decide)

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16_64 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86

theorem argsR_eq (s : State) (n : Nat) : argsR (s.gpr .esp) n = ⟨argAddr s 0, 4 * n⟩ := rfl

/-- The entry's first block: `W`, from the stack argument `w`, into `eax`. -/
theorem arg0_ok {s : State} {w : Nat} (hin : InRegions (s.rd ++ s.wr) (argA (s.gpr .esp) w) 4) :
    WP isa (.block [.mov .eax (argOp w)]) s fun s' => s'.gpr .eax = arg s w ∧ s'.gpr .esp = s.gpr .esp := by
  refine WP.of_runBlock ⟨_, by xrun [hin], ?_, ?_⟩
  · regs []; rfl
  · regs []

/-- The entry's stack arguments may be read. -/
theorem argIn_of {s : State} {n : Nat} (hA : Covers [argsR (s.gpr .esp) n] (s.rd ++ s.wr))
    (fa : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (argA (s.gpr .esp) i) 4 :=
  hA _ _ ⟨_, List.mem_singleton_self _, argA_contains hi fa⟩

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86
open VG.Spec.Gcm (StreamRepr)

/-- A streaming state is what it is outside a frame. -/
theorem streamRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 80⟩ : Region).Disjoint r) {ciph : Spec.Gcm.Block → Spec.Gcm.Block} {h : Spec.Gcm.Block}
    {iv a c : List Byte} (hr : StreamRepr m p ciph h iv a c) : StreamRepr m' p ciph h iv a c := by
  have sub : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hk r hr => (hd r hr).sub_left (Offset.sub_base _ hk)
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr ⊢
  obtain ⟨hj, ha, hc⟩ := hr
  have e0 := blockAt_frame hf (sub (d := 0) (k := 16) (by decide))
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  refine ⟨by rw [e0, hj], ha.congr (blockAt_frame hf (sub (by decide)))
    (bytesAt_frame hf (sub (d := 32) (k := (Spec.Gcm.ghashInput a c).length % 16) (by omega)) (by omega)),
    hc.congr (blockAt_frame hf (sub (by decide))) (blockAt_frame hf (sub (by decide)))⟩

end VG.Proof.AesGcm.X86

namespace VG.Proof.AesGcm.X86

open VG VG.X86

/-- A piece proven for each `i`, of code that does not depend on it: its
postcondition for all of them. -/
theorem Pc.forall {α ι : Sort _} [Inhabited ι] {P : α → State → Prop} {Q : ι → α → State → Prop} {c : Prog isa}
    (h : ∀ i, Pc P c (Q i)) : Pc P c (fun a s => ∀ i, Q i a s) := by
  refine ⟨fun a s hs => ?_, (h default).ct⟩
  obtain ⟨t, s', e, -⟩ := (h default).wp a s hs
  refine ⟨t, s', e, fun i => ?_⟩
  obtain ⟨t', s'', e', q⟩ := (h i).wp a s hs
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

end VG.Proof.AesGcm.X86
