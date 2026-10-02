import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_decode12`
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A byte, zero-extended to 32 bits (through 64). -/
abbrev z32 (b : Byte) : BitVec 32 := BitVec.setWidth 32 (BitVec.setWidth 64 b)

theorem z32_toNat (b : Byte) : (z32 b).toNat = b.toNat := by
  simp only [z32, BitVec.toNat_setWidth]; have := b.isLt; omega

/-- The 24-bit number of three bytes. -/
def w24 (c₀ c₁ c₂ : Byte) : BitVec 32 := z32 c₀ + (z32 c₁).rotateRight 24 + (z32 c₂).rotateRight 16

theorem w24_toNat (c₀ c₁ c₂ : Byte) :
    (w24 c₀ c₁ c₂).toNat = c₀.toNat + 256 * c₁.toNat + 65536 * c₂.toNat := by
  have h₀ := c₀.isLt; have h₁ := c₁.isLt; have h₂ := c₂.isLt
  rw [w24, BitVec.toNat_add, BitVec.toNat_add, rotr_toNat _ (by decide) (by rw [z32_toNat]; omega),
    rotr_toNat _ (by decide) (by rw [z32_toNat]; omega), z32_toNat, z32_toNat, z32_toNat]
  omega

theorem and4095_toNat (x : BitVec 32) : (x &&& 4095).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, show (4095 : BitVec 32).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem decode12Body_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 1) 1)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 2) 1)
    (h4 : InRegions s.wr (s.gpr .rsi) 4) (h5 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 4) 4) :
    WP isa (.block decode12Body) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi)
          (csub32 (w24 (s.mem (s.gpr .rdi)) (s.mem (s.gpr .rdi + BitVec.ofNat 64 1))
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 2)) &&& 4095))).writeW (s.gpr .rsi + BitVec.ofNat 64 4)
          (csub32 (w24 (s.mem (s.gpr .rdi)) (s.mem (s.gpr .rdi + BitVec.ofNat 64 1))
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 2)) >>> (12 : Nat))) ∧
        s'.gpr .rdi = s.gpr .rdi + 3 ∧ s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold decode12Body dec12Load dec12Fields dec12Step csubQ
  xrun [h1, h2, h3, h4, h5, List.cons_append, List.nil_append, csub32, w24, z32]
  rfl

namespace Dec12

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
end

/-- After `i` groups. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (3 * i)
  rsi : s.gpr .rsi = fP s₀ + BitVec.ofNat 64 (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (fP s₀)] s₀.mem s.mem
  done : ∀ k < 2 * i, (coeffAt s.mem (fP s₀) k).toNat = ((decode12 (bytesAt s₀.mem (bP s₀) 384))[k]!).val

section
variable {s₀ : State} (hp : decode12K.pre s₀)
include hp

theorem byte {m : Mem} (hf : Frame [pR (fP s₀)] s₀.mem m) {k : Nat} (hk : k < 384) :
    m (bP s₀ + BitVec.ofNat 64 k) = (bytesAt s₀.mem (bP s₀) 384).getD k 0 := by
  rw [bytesAt_getD _ _ hk]
  exact bytes_frame hf (by simpa using hp.2.2.1) (by decide) k hk

omit hp in
/-- A field, reduced. -/
theorem field_val {F X : Nat} (hF : F < 4096) (hX : X = F) {x : BitVec 32} (hx : x.toNat = F) :
    (csub32 x).toNat = (ofNat X).val := by
  rw [csub32_toNat (by omega), hx, val_ofNat, hX, condSub_eq (by rw [q_eq]; omega)]

theorem step {i : Nat} (hi : i < 128) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block decode12Body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have a2 : s.gpr .rsi + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * i + 1) := by
    rw [hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have a1 : s.gpr .rsi = coeffAddr (fP s₀) (2 * i) := by rw [hI.rsi]; congr 2; omega
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 384⟩, pR (fP s₀)] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [pR (fP s₀)] := by rw [hI.wr, hp.2.1]
  have hb : ∀ j < 3, s.gpr .rdi + BitVec.ofNat 64 j = bP s₀ + BitVec.ofNat 64 (3 * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hin : ∀ j < 3, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hrd, hb j hj]; exact ⟨⟨bP s₀, 384⟩, by simp, contains_offset' (by omega) (by decide)⟩
  have hout : ∀ k < 256, InRegions s.wr (coeffAddr (fP s₀) k) 4 := fun k hk => by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, coeff_contains _ hk⟩
  have hbody := decode12Body_ok s (by simpa using hin 0 (by omega)) (hin 1 (by omega)) (hin 2 (by omega))
    (by rw [a1]; exact hout _ (by omega)) (by rw [a2]; exact hout _ (by omega))
  refine WP.mono hbody fun s' ⟨⟨hm, hdi, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
  -- The three bytes and their fields.
  have e0 : s.mem (s.gpr .rdi) = (bytesAt s₀.mem (bP s₀) 384).getD (3 * i) 0 := by
    have := hb 0 (by omega); simp only [add_ofNat_zero, Nat.add_zero] at this
    rw [this, byte hp hI.frame (by omega)]
  have e1 : s.mem (s.gpr .rdi + BitVec.ofNat 64 1) = (bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 1) 0 := by
    rw [hb 1 (by omega), byte hp hI.frame (by omega)]
  have e2 : s.mem (s.gpr .rdi + BitVec.ofNat 64 2) = (bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 2) 0 := by
    rw [hb 2 (by omega), byte hp hI.frame (by omega)]
  rw [e0, e1, e2, a2, a1] at hm
  have hw := w24_toNat ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i) 0) ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 1) 0) ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 2) 0)
  have l0 := ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i) 0).isLt
  have l1 := ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 1) 0).isLt
  have l2 := ((bytesAt s₀.mem (bP s₀) 384).getD (3 * i + 2) 0).isLt
  generalize w24 _ _ _ = W at hm hw
  have lw : W.toNat < 2 ^ 24 := by omega
  have v0 : (csub32 (W &&& 4095)).toNat = ((decode12 (bytesAt s₀.mem (bP s₀) 384))[2 * i]!).val := by
    rw [decode12_even _ (bytesAt_length _ _ _) hi]
    exact field_val (F := W.toNat % 4096) (by omega) (by omega) (and4095_toNat W)
  have v1 : (csub32 (W >>> 12)).toNat = ((decode12 (bytesAt s₀.mem (bP s₀) 384))[2 * i + 1]!).val := by
    rw [decode12_odd _ (bytesAt_length _ _ _) hi]
    exact field_val (F := W.toNat / 4096) (by omega) (by omega) (by rw [shr_toNat])
  refine ⟨?_, ?_, hk.2.1.trans hI.rd, hk.2.2.trans hI.wr, ?_, fun k hk' => ?_⟩
  · rw [hdi, hI.rdi]; exact ptr_step _ i 3
  · rw [hsi, hI.rsi]; exact ptr_step _ i 8
  · rw [hm]
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * i < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * i + 1 < 256 by omega))
  · rw [hm, coeffAt_writeW _ _ (show k < 256 by omega) (show 2 * i + 1 < 256 by omega),
      coeffAt_writeW _ _ (show k < 256 by omega) (show 2 * i < 256 by omega)]
    by_cases h1 : 2 * i + 1 = k
    · subst h1; rw [ifp rfl]; exact v1
    · rw [ifn h1]
      by_cases h0 : 2 * i = k
      · subst h0; rw [ifp rfl]; exact v0
      · rw [ifn h0]; exact hI.done k (by omega)

omit hp in
theorem init {s : State} (hm : s.mem = s₀.mem) (hk : Keep [.rcx] s₀ s) : Inv s₀ 0 s :=
  ⟨by rw [hk.gpr (by decide)]; simp, by rw [hk.gpr (by decide)]; simp, hk.2.1, hk.2.2,
    by rw [hm]; exact Frame.refl _ _, fun k hk => absurd hk (by omega)⟩

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.decode12 s₀ t s' ∧ abiPreserved s₀ s' ∧
    decode12K.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.decode12)
    [.rax, .rdx, .rdi, .rsi, .rcx, .r8]
    (wp_counted (s₀ := s₀) (N := 128) (v := 128) rfl (by decide) (Inv s₀) (fun _ hm hk => init hm hk)
      fun i hi s hI => step hp hi hI) (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2)), ?_⟩
  exact polyIs_of_toNat fun k hk => hI.done k (by omega)

end

end Dec12

theorem decode12_correct (s : State) (hs : decode12K.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.decode12 s t s' ∧ abiPreserved s s' ∧ decode12K.post s s' :=
  Dec12.correct hs

theorem decode12_ct : ConstantTime isa decode12K.pre decode12K.pub Impl.MlKem.X86_64.decode12 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def decode12Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decode12_verified :
    Verified X86_64.target Impl.MlKem.X86_64.decode12 (Spec.MlKem.decode12Contract X86_64.abi) :=
  Verified.of_correct decode12_correct decode12_ct (by
    mlkem_implies [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, decode12K, X86_64.abi,
      X86_64.argRegs] [decode12Sat] using decode12Sat)

end VG.Proof.MlKem.X86_64
