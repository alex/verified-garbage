import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Ed25519.AArch64.Swap

/-! Point selection reuses the verified constant-time field swaps. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapField_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t =>
      Keep base s t ∧ t.gpr .x3 = s.gpr .x3 ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok hs (slot_range a) (slot_range b)
    (by simp only [offset]; omega) hm) fun t ⟨hg, hc, hr, hw, hsp, ⟨m, h₁, h₂, f₁⟩, _, f₂⟩ => ?_
  refine ⟨⟨hg, hr, hw, hsp, (h₁.mono (by simp only [offset]; omega) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp only [offset]; omega) (by simp only [offset]; omega))⟩, hc, ?_⟩
  rw [env_update b h₂, env_update a h₁]
  simp only [F, f₁, f₂]
  cases sw <;> rfl

theorem swapFields_ok {s : State} {base : Addr} (hs : Scr s base) (ops : List (Slot × Slot))
    (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block (swapFields ops)) s fun t =>
      Keep base s t ∧ t.gpr .x3 = s.gpr .x3 ∧ env t.mem base = swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, rfl⟩
  | cons ab ops ih =>
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hs ab.1 ab.2 (hops ab (by simp)) hm) fun t ⟨hk, hc, hv⟩ => ?_
    refine WP.mono (ih (hk.scr hs) (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (hc.trans hm))
      fun u ⟨ku, cu, vu⟩ => ?_
    refine ⟨hk.trans ku, cu.trans hc, ?_⟩
    rw [vu, hv]; rfl

end VG.Proof.Ed25519.AArch64
