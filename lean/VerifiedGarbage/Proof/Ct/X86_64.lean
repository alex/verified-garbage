import VerifiedGarbage.Impl.Ct.X86_64
import VerifiedGarbage.Proof.Ct.Common
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.TCB.X86_64.Target

namespace VG.Proof.Ct.X86_64
open VG VG.X86_64 VG.Impl.Ct.X86_64
open VG.Proof.MlKem.X86_64

def contract : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧ s.wr = []
  post s s' := (s'.gpr .rax).setWidth 32 = if Spec.Ct.eq
    (Spec.Ct.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Ct.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) then 1 else 0
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep [.rax, .r8, .r9, .r10] s₀ s ∧ s.mem = s₀.mem ∧
  s.gpr .r8 = BitVec.ofNat 64 i ∧
  s.gpr .rax = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rdx) i).setWidth 64

theorem add0 (a : Addr) : a + 0 = a := BitVec.add_zero a

theorem sub_beq (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem step_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .rcx = s₀.gpr .rsi) (i : Nat) (hi : i < (s₀.gpr .rsi).toNat)
    (h : Inv s₀ i s) :
    WP isa (.block step) s fun t => Inv s₀ (i + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rsi) := by
  obtain ⟨hk, hm, hx, ha⟩ := h
  have hdi := hk.gpr (r := .rdi) (by decide)
  have hsi := hk.gpr (r := .rsi) (by decide)
  have hdx := hk.gpr (r := .rdx) (by decide)
  have hn := (s₀.gpr .rsi).isLt
  have hrd : s.rd = s₀.rd := hk.2.1
  have hwr : s.wr = s₀.wr := hk.2.2
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    rw [hrd, hwr, hp.1, hp.2, List.append_nil]
    exact ⟨⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .rdx + BitVec.ofNat 64 i) 1 := by
    rw [hrd, hwr, hp.1, hp.2, hlen, List.append_nil]
    exact ⟨⟨s₀.gpr .rdx, (s₀.gpr .rsi).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hadd : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.ofNat_add]; rfl
  unfold step
  refine WP.mono (WP.keep [.rax, .r8, .r9, .r10] (Q := fun t => t.mem = s₀.mem ∧
      t.gpr .r8 = BitVec.ofNat 64 (i + 1) ∧
      t.gpr .rax = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rdx) (i + 1)).setWidth 64 ∧
      t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rsi)) ?_ (by rfl)) ?_
  · xrun [State.ea, hdi, hdx, hsi, hx, hm, ha, hA, hB, hadd, BitVec.mul_one,
      (show BitVec.ofInt 64 0 = 0 from rfl), add0, sub_beq, ← BitVec.setWidth_xor, ← BitVec.setWidth_or]
    rfl
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨(hk.trans hk').mono (by simp), hm', hx', ha'⟩, hz⟩

theorem loop_ok (s₀ : State) (hp : contract.pre s₀) (hlen : s₀.gpr .rcx = s₀.gpr .rsi)
    (s : State) (i : Nat) (hi : i < (s₀.gpr .rsi).toNat) (h : Inv s₀ i s) :
    WP isa (.loop (.block step) .ne) s (Inv s₀ (s₀.gpr .rsi).toNat) := by
  let n := (s₀.gpr .rsi).toNat
  apply WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧ Inv s₀ j t) ?_ (n - i) s
    ⟨i, hi, rfl, h⟩
  intro rem t ⟨j, hj, hr, hinv⟩
  refine WP.mono (step_ok s₀ t hp hlen j hj hinv) fun t' ⟨hout, hz⟩ => ?_
  by_cases he : j + 1 = n
  · left
    refine ⟨?_, (by simpa only [he] using hout)⟩
    simp [eval, hz, he, n]
  · right
    have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .rsi := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s₀.gpr .rsi).isLt; dsimp [n] at *; omega)] at this
      exact he this
    refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
    simp [eval, hz, hne]

theorem finish_ok (s : State) (d : Byte) (ha : s.gpr .rax = d.setWidth 64) :
    WP isa finish s fun t => t.mem = s.mem ∧
      (t.gpr .rax).setWidth 32 = if d = 0 then 1 else 0 := by
  unfold finish
  xrun [ha]
  exact result64 d

theorem equal_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .rcx = s₀.gpr .rsi)
    (hk : Keep [.rax, .r8, .r9, .r10] s₀ s) (hm : s.mem = s₀.mem) (ha : s.gpr .rax = 0) :
    WP isa equal s fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have hsi := hk.gpr (r := .rsi) (by decide)
  have start : WP isa (.block [.mov .r8 (.imm 0), .alu .cmp .r8 (.reg .rsi)]) s
      (fun t => Inv s₀ 0 t ∧ t.zf = some (s₀.gpr .rsi == 0)) := by
    refine WP.mono (WP.keep [.rax, .r8, .r9, .r10]
      (Q := fun t => t.mem = s₀.mem ∧ t.gpr .r8 = 0 ∧ t.gpr .rax = 0 ∧
        t.zf = some (s₀.gpr .rsi == 0)) ?_ (by rfl)) ?_
    · xrun [hm, ha, hsi, sub_beq, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl)]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact eq_comm
    · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
      exact ⟨⟨(hk.trans hk').mono (by simp), hm', hx', ha'⟩, hz⟩
  unfold equal
  refine WP.seq (WP.mono start fun t ⟨hinv, hz⟩ => WP.seq ?_)
  have after : WP isa (.ite .e (.block []) (.loop (.block step) .ne)) t
      (Inv s₀ (s₀.gpr .rsi).toNat) := by
    by_cases he : s₀.gpr .rsi = 0
    · refine WP.ite true (by simp [eval, hz, he]) (fun _ => ?_) (by simp)
      apply WP.block_nil
      simpa only [he, (show (0 : BitVec 64).toNat = 0 from rfl)] using hinv
    · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr he]) (by simp) (fun _ => ?_)
      exact loop_ok s₀ hp hlen t 0 (by bv_omega) hinv
  refine WP.mono after fun u hu => ?_
  refine WP.mono (finish_ok u _ hu.2.2.2) fun v ⟨hmv, hv⟩ => ?_
  refine ⟨hmv.trans hu.2.1, ?_⟩
  change (v.gpr .rax).setWidth 32 = _
  rw [hlen, diff_spec]
  simpa only [decide_eq_true_eq] using hv

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa eq s₀ fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have start : WP isa (.block [.mov .rax (.imm 0), .mov .r8 (.reg .rsi), .alu .cmp .r8 (.reg .rcx)]) s₀
      (fun t => Keep [.rax, .r8, .r9, .r10] s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .rax = 0 ∧
        t.zf = some (s₀.gpr .rsi == s₀.gpr .rcx)) := by
    refine WP.mono (WP.keep [.rax, .r8, .r9, .r10]
      (Q := fun t => t.mem = s₀.mem ∧ t.gpr .rax = 0 ∧
        t.zf = some (s₀.gpr .rsi == s₀.gpr .rcx)) ?_ (by rfl)) ?_
    · xrun [sub_beq, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl)]
    · intro t ⟨h, hk⟩; exact ⟨hk, h⟩
  unfold eq
  refine WP.seq (WP.mono start fun t ⟨hk, hm, ha, hz⟩ => ?_)
  by_cases he : s₀.gpr .rsi = s₀.gpr .rcx
  · exact WP.ite true (by simp [eval, hz, he])
      (fun _ => equal_ok s₀ t hp he.symm hk hm ha) (by simp)
  · refine WP.ite false (by simp [eval, hz, he]) (by simp) (fun _ => WP.block_nil ⟨hm, ?_⟩)
    have hn : (s₀.gpr .rsi).toNat ≠ (s₀.gpr .rcx).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
    simp only [contract, lengths_ne _ _ _ hn, Bool.false_eq_true, ↓reduceIte, ha]
    rfl


def sat : State where
  gpr r := match r with | .rdi => 0x1000 | .rdx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := []

theorem verified : Verified target eq (Spec.Ct.eqContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ⟨hm, ho⟩, hk⟩ := WP.keep [.rax, .r8, .r9, .r10] (correct s hp) (by rfl)
    refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ?_, ho⟩
    exact ⟨fun r hr => hk.gpr (by cases r <;> simp_all [calleeSaved]), by rw [hm]⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s t _ _ h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · sig_implies [Spec.Ct.eqContract, Spec.Ct.eqSig, contract, abi, argRegs] [sat] using sat

end VG.Proof.Ct.X86_64
