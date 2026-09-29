import VerifiedGarbage.Impl.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.PairOut
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_cbd2`

Untrusted: everything here is checked by Lean. What the code computes of
each byte is checked for each of the 256 bytes by the kernel (`cbd_vals`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The pair sums of a byte `c` (zero-extended). -/
def cbdT (c : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 c) &&& 85) +
    (BitVec.setWidth 32 (BitVec.setWidth 64 c) >>> (1 : Nat) &&& 85)

/-- Coefficient `2j` from the byte `c`. -/
def cbd0 (c : Byte) : BitVec 32 := csub32 ((cbdT c &&& 3) + qImm - (cbdT c >>> (2 : Nat) &&& 3))

/-- Coefficient `2j + 1` from the byte `c`. -/
def cbd1 (c : Byte) : BitVec 32 := csub32 ((cbdT c >>> (4 : Nat) &&& 3) + qImm - cbdT c >>> (6 : Nat))

theorem cbd_vals : ∀ n < 256, (cbd0 (BitVec.ofNat 8 n)).toNat = (cbdX n + 3329 - cbdY n) % 3329 ∧
    (cbd1 (BitVec.ofNat 8 n)).toNat = (cbdX (n / 16) + 3329 - cbdY (n / 16)) % 3329 := by
  decide +kernel

theorem cbd2Body_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1)
    (h4 : InRegions s.wr (s.gpr .rsi) 4) (h5 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 4) 4) :
    WP isa (.block cbd2Body) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi) (cbd0 (s.mem (s.gpr .rdi)))).writeW
          (s.gpr .rsi + BitVec.ofNat 64 4) (cbd1 (s.mem (s.gpr .rdi))) ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 1 ∧ s'.gpr .rsi = s.gpr .rsi + 8 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
        Keep [.rax, .rdx, .rdi, .rsi, .rcx, .r8, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cbd2Body cbdLoad cbdLo cbdHi cbdStep csubQ
  xrun [h1, h4, h5, List.cons_append, List.nil_append, csub32, cbd0, cbd1, cbdT]
  exact ⟨rfl, rfl⟩

namespace Cbd

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
/-- The value of coefficient `k`. -/
abbrev val (k : Nat) : Nat := ((samplePolyCBD 2 (bytesAt s₀.mem (bP s₀) 128))[k]!).val
end

section
variable {s₀ : State} (hp : cbd2K.pre s₀)
include hp

theorem step {i : Nat} (hi : i < 128) {s : State} (hI : PairInv s₀ (bP s₀) (fP s₀) 1 (val s₀) i s) :
    WP isa (.block cbd2Body) s fun s' => PairInv s₀ (bP s₀) (fP s₀) 1 (val s₀) (i + 1) s' ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 128⟩, pR (fP s₀)] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [pR (fP s₀)] := by rw [hI.wr, hp.2.1]
  have hb : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 i := by rw [hI.rdi, Nat.one_mul]
  have hout : ∀ k < 256, InRegions s.wr (coeffAddr (fP s₀) k) 4 := fun k hk => by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, coeff_contains _ hk⟩
  have hbody := cbd2Body_ok s (by rw [hrd, hb]; exact ⟨⟨bP s₀, 128⟩, by simp, contains_offset' (by omega) (by decide)⟩)
    (by rw [hI.addr0]; exact hout _ (by omega)) (by rw [hI.addr1]; exact hout _ (by omega))
  refine WP.mono hbody fun s' ⟨⟨hm, hdi, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
  -- The byte.
  have eb : s.mem (s.gpr .rdi) = (bytesAt s₀.mem (bP s₀) 128).getD i 0 := by
    rw [hb, bytesAt_getD _ _ hi]
    exact bytes_frame hI.frame (by simpa using hp.2.2.1) (by decide) i hi
  rw [eb, hI.addr1, hI.addr0] at hm
  have hc := cbd_vals _ ((bytesAt s₀.mem (bP s₀) 128).getD i 0).isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hc
  refine hI.step hi ?_ ?_ hm hdi hsi hk.2.1 hk.2.2
  · rw [hc.1, val, samplePolyCBD2_val _ (show 2 * i < 256 by omega)]
    simp only [nibble, Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right, Nat.pow_zero,
      Nat.div_one]
  · rw [hc.2, val, samplePolyCBD2_val _ (show 2 * i + 1 < 256 by omega)]
    simp only [nibble, show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega, Nat.pow_one]

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2 s₀ t s' ∧ abiPreserved s₀ s' ∧
    cbd2K.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.cbd2)
    [.rax, .rdx, .rdi, .rsi, .rcx, .r8, .r9]
    (wp_counted (s₀ := s₀) (N := 128) (v := 128) rfl (by decide) (PairInv s₀ (bP s₀) (fP s₀) 1 (val s₀))
      (fun _ hm hk => PairInv.init hm hk rfl rfl) fun i hi s hI => step hp hi hI) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2)), hI.polyIs fun _ _ => rfl⟩

end

end Cbd

theorem cbd2_correct (s : State) (hs : cbd2K.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2 s t s' ∧ abiPreserved s s' ∧ cbd2K.post s s' :=
  Cbd.correct hs

theorem cbd2_ct : ConstantTime isa cbd2K.pre cbd2K.pub Impl.MlKem.X86_64.cbd2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def cbd2Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem cbd2_verified :
    Verified X86_64.target Impl.MlKem.X86_64.cbd2 (Spec.MlKem.cbd2Contract X86_64.abi) :=
  Verified.of_correct cbd2_correct cbd2_ct (by
    mlkem_implies [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, cbd2K, X86_64.abi,
      X86_64.argRegs] [cbd2Sat] using cbd2Sat)

end VG.Proof.MlKem.X86_64
