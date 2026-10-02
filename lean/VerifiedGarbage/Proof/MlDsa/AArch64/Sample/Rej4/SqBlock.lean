import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oSave)

def pReg (p : Nat) : Reg := if p = 0 then .x22 else .x23
def bReg (k : Nat) : Reg := [.x24,.x25,.x26,.x27][k]!

theorem pair_regs : ∀ p < 2,
    pReg p ≠ .x16 ∧ bReg (2*p) ≠ .x6 ∧ bReg (2*p) ≠ .x7 ∧ bReg (2*p) ≠ .x16 ∧
      bReg (2*p+1) ≠ .x6 ∧ bReg (2*p+1) ≠ .x7 ∧ bReg (2*p+1) ≠ .x16 := by decide

theorem buf_word (σ : State) (k n i : Nat) : outAddr (bufAt σ k n) i = at' σ (oBuf+1008*k+168*n+8*i) := by
  unfold outAddr bufAt at'
  rw [Offset.add_add]

theorem pair_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = at' σ (400*p+16*i) := by
  unfold wordAddr stateP at'
  rw [Offset.add_add]

theorem block_regions_low {σ : State} {p n : Nat} (hp : p < 2) (hn : n < 6) :
    ∀ r ∈ [pairR (stateP σ p),outR (bufAt σ (2*p) n),outR (bufAt σ (2*p+1) n)], Region.Sub r (lowR σ) := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base (scr σ) (by dsimp only [oSave]; omega)
  · exact Offset.sub_base (scr σ) (by dsimp only [oBuf,oSave]; omega)
  · exact Offset.sub_base (scr σ) (by dsimp only [oBuf,oSave]; omega)

/-- One pair's permutation and rate output, inside the four-way sampler. -/
theorem pairBlock_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) (he : Env σ s) {p n : Nat} (hpn : p < 2) (hn : n < 6)
    {A B : Spec.Sha3.State}
    (hx : s.gpr (pReg p) = stateP σ p)
    (ha : s.gpr (bReg (2*p)) = bufAt σ (2*p) n)
    (hb : s.gpr (bReg (2*p+1)) = bufAt σ (2*p+1) n)
    (hpair : PairAt s.mem (stateP σ p) A B) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 (pReg p) (bReg (2*p)) (bReg (2*p+1))) s
      fun t => Env σ t ∧ BlockKeep s t ∧
        PairAt t.mem (stateP σ p) (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
        RateAt t.mem (bufAt σ (2*p) n) (Spec.Sha3.keccakF A) ∧
        RateAt t.mem (bufAt σ (2*p+1) n) (Spec.Sha3.keccakF B) ∧
        Frame [pairR (stateP σ p),outR (bufAt σ (2*p) n),outR (bufAt σ (2*p+1) n)] s.mem t.mem := by
  obtain ⟨hp16,ha6,ha7,ha16,hb6,hb7,hb16⟩ := pair_regs p hpn
  refine WP.mono (prog_okWith sha3 hx ha hb ha6 ha7 ha16 hb6 hb7 hb16 hp16 hpair
    (fun i hi => by rw [pair_word]; exact in_scr_rd hp he.rd he.wr (by omega))
    (fun i hi => by rw [pair_word]; exact in_scr hp he.wr (by omega))
    (fun i hi => by rw [buf_word]; exact in_scr hp he.wr (by dsimp only [oBuf]; omega))
    (fun i hi => by rw [buf_word]; exact in_scr hp he.wr (by dsimp only [oBuf]; omega))
    (Offset.disjoint (scr σ) (d := oBuf+1008*(2*p)+168*n) (n := 168)
      (e := oBuf+1008*(2*p+1)+168*n) (k := 168) (by omega)
      (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)))
    fun t ⟨ht,hpt,hat,hbt,hft⟩ => ?_
  exact ⟨he.lowStep hft (block_regions_low hpn hn) ht.rd ht.wr ht.sp (fun r hr => ht.gpr r
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    ht,hpt,hat,hbt,hft⟩
end VG.Proof.MlDsa.AArch64.Sample.Rej4
