import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.Points

/-! Point selection reuses the verified constant-time field swaps. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr mask F cswap_ok)

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapField_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (VG.Impl.X25519.X86_64.cswap (offset a) (offset b))) s fun t =>
      Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok hs (by simp only [offset]; omega) (by simp only [offset]; omega)
    (by simp only [offset]; omega) hm) fun t ⟨hg, hc, hr, hw, ⟨m, h₁, h₂, f₁⟩, _, f₂⟩ => ?_
  refine ⟨⟨hg, hr, hw, (h₁.mono (by simp only [offset]; omega) (by simp only [offset]; omega)).trans
    (h₂.mono (by simp only [offset]; omega) (by simp only [offset]; omega))⟩, hc, ?_⟩
  rw [env_update b h₂, env_update a h₁]
  simp only [F, f₁, f₂]
  cases sw <;> rfl

theorem swapFieldWide_ok {s : State} {base : Addr} (hs : Scratch s base) (a b : Slot)
    (hab : a ≠ b) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (VG.Impl.X25519.X86_64.cswap (offset a) (offset b))) s fun t =>
      Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hc, hv⟩ := swapField_ok hn a b hab hm
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hc, hv⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem swapFieldsWide_ok {s : State} {base : Addr} (hs : Scratch s base) (ops : List (Slot × Slot))
    (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (swapFields ops)) s fun t =>
      Keep base s t ∧ t.gpr .rcx = s.gpr .rcx ∧ env t.mem base = swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, rfl⟩
  | cons ab ops ih =>
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapFieldWide_ok hs ab.1 ab.2 (hops ab (by simp)) hm) fun t ⟨hk, hc, hv⟩ => ?_
    refine WP.mono (ih (hs.of_keep hk) (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (hc.trans hm))
      fun u ⟨ku, cu, vu⟩ => ?_
    refine ⟨hk.trans ku, cu.trans hc, ?_⟩
    rw [vu, hv]; rfl

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by
  cases sw <;> rfl

theorem pointSelect_d (e : Env) (sw : Bool) : swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : Addr} (hs : Scratch s base) {sw : Bool}
    (hm : s.gpr .rcx = mask sw) :
    WP isa (.block pointSelect) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 =
        (if sw then point (env s.mem base) 17 18 19 20 else point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.mono (swapFieldsWide_ok hs pointSelectPairs (by decide) hm) fun t ⟨hk, _, hv⟩ => ?_
  exact ⟨hk, by rw [hv, pointSelect_eval], by rw [hv, pointSelect_d]⟩

end VG.Proof.Ed25519.X86_64
