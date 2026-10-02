import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Loop
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA on x86-64: the functions with `γ₂` and one output

`vg_mldsa_high_bits`, `vg_mldsa_low_bits` and `vg_mldsa_use_hint` compare `γ₂`
(in `gr`) with `(q - 1)/32`, move their output pointer (in `oa`) to `r10`, and
run the loop of the body for the `γ₂` they found. `oneOut_ok` proves this
once, from a body that stores `F γ₂ x` for the coefficients `x p` of the
inputs `p`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt gamma2s)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero32 (x k : BitVec 32) : (x - k == 0) = decide (x = k) := by
  by_cases h : x = k
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; bv_omega

theorem gamma_cases {s₀ : State} {gr : Reg} (hg : arg32 s₀ gr ∈ gamma2s) :
    (BitVec.setWidth 32 (s₀.gpr gr) = BitVec.ofNat 32 g32 → arg32 s₀ gr = g32) ∧
      (BitVec.setWidth 32 (s₀.gpr gr) ≠ BitVec.ofNat 32 g32 → arg32 s₀ gr = g88) := by
  refine ⟨fun h => by rw [arg32, h]; rfl, fun h => ?_⟩
  rcases mem_gamma2s hg with e | e
  · exact e
  · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h

/-- What the prologue does: `γ₂` compared, and the output pointer in `r10`. -/
def Prologue (gr oa : Reg) (s s' : State) : Prop :=
  (s'.gpr .r10 = s.gpr oa ∧ s'.zf = some (BitVec.setWidth 32 (s.gpr gr) - BitVec.ofNat 32 g32 == 0) ∧
    s'.mem = s.mem) ∧ Keep [gr, .r10] s s'

theorem prologue_rsi_rdx (s : State) :
    WP isa (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) s (Prologue .rsi .rdx s) := by
  refine WP.keep _ ?_ (by decide)
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem prologue_rdx_rcx (s : State) :
    WP isa (.block (gammaCmp .rdx ++ ([.mov .r10 (.reg .rcx)] : List Instr))) s (Prologue .rdx .rcx s) := by
  refine WP.keep _ ?_ (by decide)
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem oneOut_ok {s₀ : State} {ins : List Reg} {gr oa : Reg} {clob : List Reg} {body : Nat → List Instr}
    {F : Nat → List (BitVec 32) → BitVec 32}
    (hrd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd) (hwr : s₀.wr = [pR (s₀.gpr oa)])
    (hdis : ∀ p ∈ ins, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr oa))) (hg : arg32 s₀ gr ∈ gamma2s)
    (hpro : WP isa (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) s₀ (Prologue gr oa s₀)) (hins : ∀ p ∈ ins, p ≠ gr ∧ p ≠ .r10) (hfix : ∀ r ∈ Reg.r10 :: ins, r ∉ clob)
    (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ ins, InRegions (s.rd ++ s.wr) (cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g (ins.map fun p => s.mem.readW (cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr oa) k = F (arg32 s₀ gr) (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k)) ∧
          Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
  refine WP.seq (WP.mono hpro fun s₁ ⟨⟨h10, hz, hm⟩, hk⟩ => ?_)
  have hp : ∀ p ∈ ins, s₁.gpr p = s₀.gpr p := fun p hp' =>
    hk.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hins p hp')
  have hL : Layout s₁ ins [.r10] :=
    { rd := fun p hp' => by rw [hp p hp', hk.2.1, hk.2.2]; exact List.mem_append_left _ (hrd p hp')
      wr := fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hk.2.2, hwr]; exact List.mem_singleton_self _
      dis := fun p hp' o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hp p hp']; exact hdis p hp'
      pw := List.pairwise_singleton _ _ }
  have go : ∀ g, arg32 s₀ gr = g → WP isa (mapLoop (body g)) s₁ fun s' =>
      (∀ k < 256, coeffAt s'.mem (s₀.gpr oa) k = F (arg32 s₀ gr) (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k)) ∧
        Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
    intro g hge
    refine WP.mono (loop_ok (fixed := .r10 :: ins) (V := fun _ k => F g (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k))
      (J := fun _ _ => True) hL hfix hcx (fun _ _ _ _ => trivial) fun i hi s hI hc => ?_) fun s' hI => ?_
    · have ha : ∀ p ∈ Reg.r10 :: ins, cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₁.gpr p) (255 - i) :=
        fun p hp' => hI.addr hc hi hp'
      have hg' : g = g32 ∨ g = g88 := by
        rcases mem_gamma2s hg with e | e <;> rw [e] at hge <;> subst hge <;> decide
      refine WP.mono (hbody g hg' s (fun p hp' => by
          rw [ha p (List.mem_cons_of_mem _ hp')]; exact hI.inR hL hp' (by omega))
        (by rw [ha _ List.mem_cons_self]; exact hI.inW hL List.mem_cons_self (by omega)))
        fun s' ⟨⟨hm', hc', hz'⟩, hk'⟩ => ⟨⟨?_, hc', hz', trivial⟩, hk'⟩
      rw [hm', ha _ List.mem_cons_self]
      refine congrArg (Mem.writeW _ _ <| F g ·) (List.map_congr_left fun p hp' => ?_)
      rw [ha p (List.mem_cons_of_mem _ hp'), hI.read hL hp' (by omega), hm, hp p hp']
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [← h10, hI.done .r10 List.mem_cons_self k (by omega) hk, hge]
      · have := hI.frame
        rw [hm, List.map_singleton, h10] at this
        exact this
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hz) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact go _ ((gamma_cases hg).1 h)
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    exact go _ ((gamma_cases hg).2 h)

end VG.Proof.MlDsa.X86_64.Round
