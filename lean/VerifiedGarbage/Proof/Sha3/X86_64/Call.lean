import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# SHA-3 on x86-64: calling the permutation

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_keeps : ((instrs permute).all fun i => Taint.dstOf i != some .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem permute_nosp : NoSp permute := by
  intro i hi
  simpa using List.all_eq_true.mp permute_keeps i hi

theorem permute_depth : permute.depth = 0 := by decide +kernel

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- Calling `vg_keccak_f1600` on the state at `rdi`, with scratch space at
`rsi`. -/
theorem call_ok {s : State} {st scr : Addr} (hdi : s.gpr .rdi = st) (hsi : s.gpr .rsi = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) →
      s'.gpr .rdi = st → s'.gpr .rsi = scr → Q s') :
    WP isa (.call "vg_keccak_f1600" permute) s Q := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Sha3.permuteX86_64) permute_verified.1 permute_nosp
    (by rw [permute_depth]; decide) (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_
  · simp only [Proof.Sha3.permuteX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hdi, hsi]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hdi₂, hsi₂⟩
    simp only [State.withRegions_gpr, State.withRegions_mem, hne _ (by decide : Reg.rdi ≠ .rsp), hdi,
      hm₂] at hpost hdi₂
    simp only [State.withRegions_gpr, hne _ (by decide : Reg.rsi ≠ .rsp), hsi] at hsi₂
    have hst : stateAt s.callEntry.mem st = stateAt s.mem st :=
      Proof.Sha3.stateAt_congr fun i hi => callEntry_byte s (R := ⟨st, 200⟩) d₂ (by simp) hi
    refine hQ s' hrd hwr hcs (by rw [permute_depth] at hf; simpa using hf) (by rw [hpost, hst])
      (by rw [← hg₂ _ (by decide), hdi₂]) (by rw [← hg₂ _ (by decide), hsi₂])

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `rbx`, with
scratch space at `r15`. -/
theorem permuteAt_ok {s : State} {st scr : Addr} (hbx : s.gpr .rbx = st) (h15 : s.gpr .r15 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa Impl.Sha3.X86_64.Stream.permuteAt s Q := by
  unfold Impl.Sha3.X86_64.Stream.permuteAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_nil ?_)
  have sp₂ : s₂.gpr .rsp = s.gpr .rsp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [u₂.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine WP.seq (call_ok (st := st) (scr := scr)
    (by rw [u₂.other _ (by decide), u₁.gpr, hbx]) (by rw [u₂.gpr, u₁.other _ (by decide), h15])
    d₁ (by rw [sp₂]; exact d₂) (by rw [sp₂]; exact d₃) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ rd₃ wr₃ cs₃ f₃ e₃ di₃ si₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_nil ?_)
  refine hQ s₅ (by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
    (fun r hr => ?_) (by rw [u₅.mem, u₄.mem, ← u₁.mem, ← u₂.mem, ← sp₂]; exact f₃)
    (by rw [u₅.mem, u₄.mem, e₃, u₂.mem, u₁.mem])
  by_cases h1 : r = .r15
  · subst h1; rw [u₅.gpr, u₄.other _ (by decide), si₃, h15]
  · by_cases h2 : r = .rbx
    · subst h2; rw [u₅.other _ (by decide), u₄.gpr, di₃, hbx]
    · rw [u₅.other _ h1, u₄.other _ h2, cs₃ r hr, cs₂ r hr]

end VG.Proof.Sha3.X86_64
