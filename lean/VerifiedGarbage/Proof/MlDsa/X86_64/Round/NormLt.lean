import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Loop
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ML-DSA on x86-64: `vg_mldsa_norm_lt`

The top bit of `r9` stays set while every coefficient `a` so far has `a <
bound` or `q - a < bound` (`Good`), which is `‖a‖∞ < bound` (`normZq_lt`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of setReg_gpr setReg_mem)

/-- The value the body ands into `r9`: its top bit is whether `a < B` or `q - a < B`. -/
def nlV (x : BitVec 32) (B : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 x - B ||| BitVec.setWidth 64 qImm - BitVec.setWidth 64 x - B

theorem nlBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4) :
    WP isa (.block (nlBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .r9 = s.gpr .r9 &&& nlV (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32) (s.gpr .rsi) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r9, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold nlBody
  xrun [h1, ea_cf, List.cons_append, List.nil_append, nlV]

/-- The top bit of a difference of numbers below `2⁶³`: whether it borrows. -/
theorem msb_sub {u v : BitVec 64} (hu : u.toNat < 2 ^ 63) (hv : v.toNat < 2 ^ 63) :
    (u - v).msb = decide (u.toNat < v.toNat) := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases h : u.toNat < v.toNat
  · rw [decide_eq_true h, decide_eq_true_iff]; omega
  · rw [decide_eq_false h, decide_eq_false_iff_not]; omega

/-- Whether `a < B` or `q - a < B`. -/
abbrev Good (B a : Nat) : Prop := a < B ∨ q - a < B

theorem nlV_msb {x : BitVec 32} (hx : x.toNat < q) {B : BitVec 64} (hB : B.toNat < 2 ^ 32) :
    (nlV x B).msb = decide (Good B.toNat x.toNat) := by
  have hq : (BitVec.setWidth 64 qImm).toNat = q := rfl
  have e : (BitVec.setWidth 64 qImm - BitVec.setWidth 64 x).toNat = q - x.toNat := by
    rw [BitVec.toNat_sub, hq, setWidth64_toNat]; rw [q_eq] at hx ⊢; omega
  rw [nlV, BitVec.msb_or, msb_sub (by rw [setWidth64_toNat]; have := x.isLt; omega) (by omega),
    msb_sub (by rw [e, q_eq]; omega) (by omega), e, setWidth64_toNat]
  simp only [Good, Bool.decide_or]

section
variable {s₀ : State} (hp : normLtK.pre s₀)
include hp

/-- The loop, from `s₁`, the state after the prologue. -/
theorem nl_loop {s₁ : State} (hdi : s₁.gpr .rdi = s₀.gpr .rdi) (hsi : s₁.gpr .rsi = BitVec.setWidth 64 ((s₀.gpr .rsi).setWidth 32))
    (h9 : s₁.gpr .r9 = BitVec.allOnes 64) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = s₀.mem) :
    WP isa (mapLoop nlBody) s₁ (Inv s₁ [.rdi, .rsi] [] (fun _ _ => 0) (fun i s =>
      ((s.gpr .r9).msb = true ↔ ∀ k, 256 - i ≤ k → k < 256 →
        Good (arg32 s₀ .rsi) (coeffAt s₀.mem (s₀.gpr .rdi) k).toNat)) 256) := by
  have hL : Layout s₁ [.rdi] [] :=
    { rd := fun p h => by
        simp only [List.mem_singleton] at h; subst h; rw [hrd, hwr, hp.1, hdi]; simp
      wr := fun _ h => by cases h
      dis := fun _ _ _ h => by cases h
      pw := List.Pairwise.nil }
  have hB : (s₁.gpr .rsi).toNat = arg32 s₀ .rsi := by rw [hsi, setWidth64_toNat]
  refine loop_ok (clob := [.rax, .rdx, .r9, .rcx]) hL (by decide) (by decide) (fun s _ _ hk => ?_)
    fun i hi s hI hc => ?_
  · rw [hk.gpr (by decide), h9]
    exact iff_of_true (by decide) fun k h₁ h₂ => absurd h₂ (by omega)
  · have ha : cfAddr (s.gpr .rdi) (s.gpr .rcx) = coeffAddr (s₁.gpr .rdi) (255 - i) :=
      hI.addr hc hi (by simp)
    refine WP.mono (nlBody_ok s (by rw [ha]; exact hI.inR hL (by simp) (by omega)))
      fun s' ⟨⟨hm', h9', hc', hz'⟩, hk'⟩ => ⟨⟨hm', hc', hz', ?_⟩, hk'⟩
    have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2
    have hx := hr (255 - i) (by rw [n_eq]; omega)
    rw [h9', BitVec.msb_and, Bool.and_eq_true, hI.j, ha, hI.read hL (by simp) (by omega), hI.fixed .rsi (by simp),
      nlV_msb (by rw [hm, hdi]; exact hx) (by rw [hsi, setWidth64_toNat]; exact BitVec.isLt _), hB, hm, hdi,
      decide_eq_true_iff]
    refine ⟨fun ⟨h₁, h₂⟩ k hk₁ hk₂ => ?_, fun h => ⟨fun k hk₁ hk₂ => h k (by omega) hk₂,
      h _ (by omega) (by omega)⟩⟩
    by_cases e : k = 255 - i
    · subst e; exact h₂
    · exact h₁ k (by omega) hk₂

theorem nl_correct : ∃ t s', Exec isa normLt s₀ t s' ∧ abiPreserved s₀ s' ∧ normLtK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2
  have hpro : WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r9 (.imm 0xFFFFFFFF)]) s₀ fun s₁ =>
      (s₁.gpr .rsi = BitVec.setWidth 64 ((s₀.gpr .rsi).setWidth 32) ∧ s₁.gpr .r9 = BitVec.allOnes 64 ∧
        s₁.mem = s₀.mem) ∧ Keep [.rsi, .r9] s₀ s₁ := by
    refine WP.keep _ ?_ (by decide)
    xrun
  have hpost : ∀ s : State, WP isa (.block [.mov .rax (.reg .r9), .shift .shr .rax 63]) s fun s' =>
      (s'.gpr .rax = s.gpr .r9 >>> 63 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := fun s => by
    refine WP.keep _ ?_ (by decide)
    xrun
  have hnorm : normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi ↔
      ∀ k, 256 - 256 ≤ k → k < 256 → Good (arg32 s₀ .rsi) (coeffAt s₀.mem (s₀.gpr .rdi) k).toNat := by
    rw [normRq_lt]
    refine ⟨fun h k _ hk => ?_, fun h k hk => ?_⟩
    · have := h k hk; rwa [normZq_lt, polyAt_val hr hk] at this
    · rw [normZq_lt, polyAt_val hr hk]; exact h k (by omega) hk
  have wp : WP isa normLt s₀ fun s' =>
      ((s'.gpr .rax).setWidth 32 = if normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi then 1 else 0) ∧
        Frame [] s₀.mem s'.mem := by
    refine WP.seq (WP.mono hpro fun s₁ ⟨⟨hsi, h9, hm⟩, hk⟩ => ?_)
    refine WP.seq (WP.mono (nl_loop hp (hk.gpr (by decide)) hsi h9 hk.2.1 hk.2.2 hm) fun s₂ hI => ?_)
    refine WP.mono (hpost s₂) fun s' ⟨⟨hax, hm'⟩, _⟩ => ⟨?_, ?_⟩
    · have hj := hI.j
      rw [← hnorm] at hj
      rw [hax]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hlt := (s₂.gpr .r9).isLt
      have hmsb := BitVec.msb_eq_decide (s₂.gpr .r9)
      by_cases h : normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
        have := hj.mpr h
        rw [hmsb, decide_eq_true_iff] at this
        show _ = 1
        omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
        have : (s₂.gpr .r9).msb = false := by
          cases e : (s₂.gpr .r9).msb
          · rfl
          · exact absurd (hj.mp e) h
        rw [hmsb, decide_eq_false_iff_not] at this
        show _ = 0
        omega
    · have := hI.frame
      rw [hm'] at ⊢
      rw [hm] at this
      exact this
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r9] wp (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf (by simp)), hv⟩

end

theorem normLt_ct : ConstantTime isa normLtK.pre normLtK.pub normLt :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def normSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem normLt_verified : Verified X86_64.target normLt (normLtContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => nl_correct hp) normLt_ct (by
    round_implies [normLtContract, normLtSig, normLtK, X86_64.abi, X86_64.argRegs] [normSat] using normSat)

end VG.Proof.MlDsa.X86_64.Round
