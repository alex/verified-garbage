import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_encode12`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The byte a `store8` of a 32-bit value stores. -/
abbrev b8 (x : BitVec 32) : Byte := BitVec.setWidth 8 (BitVec.setWidth 64 x)

/-- The 24-bit number of a pair of 12-bit values. -/
theorem pair_val {A B : BitVec 32} (ha : A.toNat < 4096) (hb : B.toNat < 4096) :
    (A + B.rotateRight 20).toNat = A.toNat + 4096 * B.toNat := by
  rw [BitVec.toNat_add, rotr_toNat B (by decide) (by omega)]
  omega

theorem encode12Body_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 4) 4)
    (h3 : InRegions s.wr (s.gpr .rsi) 1) (h4 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h5 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa (.block encode12Body) s fun s' =>
      (s'.mem = ((s.mem.writeW (s.gpr .rsi) (b8 (s.mem.readW (s.gpr .rdi) 32 +
          (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 4) 32).rotateRight 20))).writeW
          (s.gpr .rsi + BitVec.ofNat 64 1) (b8 ((s.mem.readW (s.gpr .rdi) 32 +
          (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 4) 32).rotateRight 20) >>> 8))).writeW
          (s.gpr .rsi + BitVec.ofNat 64 2) (b8 ((s.mem.readW (s.gpr .rdi) 32 +
          (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 4) 32).rotateRight 20) >>> 8 >>> 8)) ∧
        s'.gpr .rdi = s.gpr .rdi + 8 ∧ s'.gpr .rsi = s.gpr .rsi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold encode12Body enc12Pair enc12Store enc12Step
  xrun [h1, h2, h3, h4, h5, List.cons_append, List.nil_append]

namespace Enc12

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rsi
abbrev F : Poly := polyAt s₀.mem (fP s₀)
end

/-- After `i` pairs. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = fP s₀ + BitVec.ofNat 64 (8 * i)
  rsi : s.gpr .rsi = oP s₀ + BitVec.ofNat 64 (3 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨oP s₀, 384⟩] s₀.mem s.mem
  done : ∀ k < 3 * i, s.mem (oP s₀ + BitVec.ofNat 64 k) = (encode12 (F s₀))[k]!

section
variable {s₀ : State} (hp : encode12K.pre s₀)
include hp

theorem coeff {m : Mem} (hf : Frame [⟨oP s₀, 384⟩] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (fP s₀) k = coeffAt s₀.mem (fP s₀) k :=
  coeffAt_congr (bytes_frame hf (by simpa using hp.2.2.1) (by decide)) hk

theorem step {i : Nat} (hi : i < 128) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block encode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have a1 : s.gpr .rdi = coeffAddr (fP s₀) (2 * i) := by
    rw [hI.rdi]; congr 2; omega
  have a2 : s.gpr .rdi + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * i + 1) := by
    rw [a1, coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  have hrd : s.rd ++ s.wr = [pR (fP s₀), ⟨oP s₀, 384⟩] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [⟨oP s₀, 384⟩] := by rw [hI.wr, hp.2.1]
  have ho : ∀ j < 3, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hwr, hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  have hin : ∀ k < 256, InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) k) 4 := fun k hk => by
    rw [hrd]; exact ⟨_, by simp, coeff_contains _ hk⟩
  have hb := encode12Body_ok s (by rw [a1]; exact hin _ (by omega)) (by rw [a2]; exact hin _ (by omega))
    (by simpa using ho 0 (by omega)) (ho 1 (by omega)) (ho 2 (by omega))
  refine WP.mono hb fun s' ⟨⟨hm, hdi, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
  -- The pair and its 24-bit number.
  have hr : Reduced s₀.mem (fP s₀) := hp.2.2.2.2.2
  have eA : s.mem.readW (s.gpr .rdi) 32 = coeffAt s₀.mem (fP s₀) (2 * i) := by
    rw [a1, ← coeffAt_eq, coeff hp hI.frame (show 2 * i < 256 by omega)]
  have eB : s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 4) 32 = coeffAt s₀.mem (fP s₀) (2 * i + 1) := by
    rw [a2, ← coeffAt_eq, coeff hp hI.frame (show 2 * i + 1 < 256 by omega)]
  have hA : (coeffAt s₀.mem (fP s₀) (2 * i)).toNat < 3329 := hr (2 * i) (show 2 * i < 256 by omega)
  have hB : (coeffAt s₀.mem (fP s₀) (2 * i + 1)).toNat < 3329 :=
    hr (2 * i + 1) (show 2 * i + 1 < 256 by omega)
  have hW := pair_val (A := coeffAt s₀.mem (fP s₀) (2 * i)) (B := coeffAt s₀.mem (fP s₀) (2 * i + 1))
    (by omega) (by omega)
  rw [eA, eB] at hm
  generalize coeffAt s₀.mem (fP s₀) (2 * i) + (coeffAt s₀.mem (fP s₀) (2 * i + 1)).rotateRight 20 = W at hm hW
  have hX : (coeffAt s₀.mem (fP s₀) (2 * i)).toNat + 4096 * (coeffAt s₀.mem (fP s₀) (2 * i + 1)).toNat =
      ((F s₀)[2 * i]!).val + 4096 * ((F s₀)[2 * i + 1]!).val := by
    rw [polyAt_val hr (show 2 * i < 256 by omega), polyAt_val hr (show 2 * i + 1 < 256 by omega)]
  -- The three bytes.
  have hw : Written s.mem s'.mem (oP s₀ + BitVec.ofNat 64 (3 * i)) 3
      fun j => (encode12 (F s₀))[3 * i + j]! := by
    rw [hm, hI.rsi]
    refine (((Written.first _ _ _).snoc (by decide) _).snoc (by decide) _).congr fun j hj => ?_
    rw [encode12_group _ hi hj, ← hX, ← hW]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [↓reduceIte, b8_eq, shr_toNat, Nat.div_div_eq_div_mul,
        Nat.reduceMul, Nat.reducePow, Nat.div_one]
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hw (by omega) (by decide)
  refine ⟨?_, ?_, hk.2.1.trans hI.rd, hk.2.2.trans hI.wr, hf', fun k hk' => hd' k (by omega)⟩
  · rw [hdi, hI.rdi]; exact ptr_step _ i 8
  · rw [hsi, hI.rsi]; exact ptr_step _ i 3

omit hp in
theorem init {s : State} (hm : s.mem = s₀.mem) (hk : Keep [.rcx] s₀ s) : Inv s₀ 0 s :=
  ⟨by rw [hk.gpr (by decide)]; simp, by rw [hk.gpr (by decide)]; simp, hk.2.1, hk.2.2,
    by rw [hm]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.encode12 s₀ t s' ∧ abiPreserved s₀ s' ∧
    encode12K.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.encode12) [.rax, .rdx, .rdi, .rsi, .rcx]
    (wp_counted (s₀ := s₀) (N := 128) (v := 128) rfl (by decide) (Inv s₀) (fun _ hm hk => init hm hk)
      fun i hi s hI => step hp hi hI) (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2.1)), ?_⟩
  exact bytesAt_eq! (encode12_length _) fun k hk => hI.done k (by omega)

end

end Enc12

theorem encode12_correct (s : State) (hs : encode12K.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.encode12 s t s' ∧ abiPreserved s s' ∧ encode12K.post s s' :=
  Enc12.correct hs

theorem encode12_ct : ConstantTime isa encode12K.pre encode12K.pub Impl.MlKem.X86_64.encode12 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def encode12Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 384⟩]

theorem encode12_verified :
    Verified X86_64.target Impl.MlKem.X86_64.encode12 (Spec.MlKem.encode12Contract X86_64.abi) :=
  Verified.of_correct encode12_correct encode12_ct (by
    mlkem_implies [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, encode12K, X86_64.abi,
      X86_64.argRegs] [encode12Sat] using encode12Sat)

end VG.Proof.MlKem.X86_64
