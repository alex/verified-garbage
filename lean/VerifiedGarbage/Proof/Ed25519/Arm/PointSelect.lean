import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect
import VerifiedGarbage.Proof.Ed25519.Arm.Points

/-! Untrusted: branch-free selection using the verified limb swaps. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def swapSlot (a b : Slot) (sw : Bool) (i : Slot) : Slot :=
  if sw then if i = a then b else if i = b then a else i else i

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env := fun i => e (swapSlot a b sw i)
def swapEnvs (ops : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  ops.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapEnvs_step (ops : List (Slot × Slot)) (a b : Slot) (sw : Bool) {e f g : Env}
    (hf : f = swapEnv a b sw e) (hg : g = swapEnvs ops sw f) :
    g = swapEnvs ((a, b) :: ops) sw e := hg.trans (congrArg (swapEnvs ops sw) hf)

theorem swapField_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) (hab : a ≠ b) {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (cswap (offset a) (offset b))) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnv a b sw (env s.mem base) := by
  have ha := slot_range a
  have hb := slot_range b
  rw [ACC_eq] at ha hb
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine WP.mono (cswap_ok (by omega) (by omega) (by simp only [offset]; omega) hc
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ht => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr base) (offset i) k =
      limb s.mem (State.addr base) (offset (swapSlot a b sw i)) k := by
    intro i k hk
    by_cases hia : i = a
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, sel, Bool.toNat_false, Bool.toNat_true, zero_ne_one] using ht.lx k hk
    by_cases hib : i = b
    · subst i
      cases sw <;> simpa only [swapSlot, Bool.false_eq_true, ite_false, ite_true, hia, sel, Bool.toNat_false, Bool.toNat_true, zero_ne_one] using ht.ly k hk
    · have hn1 : i.val ≠ a.val := fun h => hia (Fin.ext h)
      have hn2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
      have hi := slot_range i
      rw [ACC_eq] at hi
      have ei : swapSlot a b sw i = i := by simp only [swapSlot, hia, hib, ite_false, ite_self]
      rw [ei]
      refine limb_frame ht.frame (fun r hr j hj => ?_) k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (by simp only [offset]; omega) (by omega) (by omega)
  refine ⟨⟨ht.rest.mono (by decide), ?_⟩,
    fun i k hk => by rw [he i k hk]; exact hl _ k hk,
    ht.rest.gpr _ (by decide), funext fun i => congrArg VG.Proof.X25519.toFe (val16_congr (he i))⟩
  refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)

theorem swapFields_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (ops : List (Slot × Slot)) (hops : ∀ ab ∈ ops, ab.1 ≠ ab.2) {sw : Bool}
    (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block (swapFields ops)) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      t.gpr .r9 = s.gpr .r9 ∧ env t.mem base = swapEnvs ops sw (env s.mem base) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl, rfl⟩
  | cons ab ops ih =>
    rcases ab with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc hl a b (hops (a, b) (by simp)) hm) fun t ⟨hk, hlt, ht9, hv⟩ => ?_
    refine WP.mono (ih (hk.ctx hc) hlt (fun p hp => hops p (List.mem_cons_of_mem _ hp)) (ht9.trans hm))
      fun u ⟨ku, hlu, hu9, vu⟩ => ?_
    refine ⟨hk.trans ku, hlu, hu9.trans ht9, ?_⟩
    exact swapEnvs_step ops a b sw (e := env s.mem base) (f := env t.mem base) (g := env u.mem base) hv vu

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapEnvs pointSelectPairs sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by cases sw <;> rfl

theorem pointSelect_d (e : Env) (sw : Bool) : swapEnvs pointSelectPairs sw e 16 = e 16 := by
  cases sw <;> rfl

theorem pointSelect_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    {sw : Bool} (hm : s.gpr .r9 = 0 - BitVec.ofNat 32 sw.toNat) :
    WP isa (.block pointSelect) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      point (env t.mem base) 0 1 2 3 =
        (if sw then point (env s.mem base) 17 18 19 20 else point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = env s.mem base 16 := by
  refine WP.mono (swapFields_ok hc hl pointSelectPairs (by decide) hm) fun t ⟨hk, hlt, _, hv⟩ => ?_
  exact ⟨hk, hlt, by rw [hv, pointSelect_eval], by rw [hv, pointSelect_d]⟩

end VG.Proof.Ed25519.Arm
