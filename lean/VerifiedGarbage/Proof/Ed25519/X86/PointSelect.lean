import VerifiedGarbage.Impl.Ed25519.X86.PointSelect
import VerifiedGarbage.Proof.Ed25519.X86.Points

/-! Field and point selection by a fixed sequence of masked swaps. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def swapEnv (a b : Slot) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e a (if sw then e b else e a)) b (if sw then e a else e b)

def swapsEnv (pairs : List (Slot × Slot)) (sw : Bool) (e : Env) : Env :=
  pairs.foldl (fun e (a, b) => swapEnv a b sw e) e

theorem swapField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a b : Slot) (hab : a ≠ b)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (VG.Impl.X25519.X86.cswap (offset a) (offset b))) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapEnv a b sw (env s.mem x) := by
  have sep := slot_ne (slot_valid b) (slot_valid a) (fun h => hab (offset_inj h))
  refine WP.mono (cswap_ok hc (slot_below (slot_valid a)) (slot_below (slot_valid b)) sep
    (show sw.toNat ≤ 1 by cases sw <;> decide) hm) fun t ⟨hk, hm', hf, ha, hb⟩ => ?_
  have wide : Frame [sub x 64 864] s.mem t.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 64 864, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
    · exact sub_sub hc.fit (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)
  refine ⟨⟨hk, wide⟩, hm', ?_⟩
  have hfit := hc.fit
  funext i
  by_cases hia : i = a
  · subst i
    rw [swapEnv, Function.update_of_ne hab, Function.update_self]
    change VG.Proof.X25519.toFe (fe t.mem x (offset a)) = _
    rw [ha]
    cases sw <;> rfl
  · by_cases hib : i = b
    · subst i
      rw [swapEnv, Function.update_self]
      change VG.Proof.X25519.toFe (fe t.mem x (offset b)) = _
      rw [hb]
      cases sw <;> rfl
    · rw [swapEnv, Function.update_of_ne hib, Function.update_of_ne hia]
      apply congrArg VG.Proof.X25519.toFe
      apply fe_frame
      intro k hk'
      apply wd_frame hf
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hs := slot_ne (slot_valid a) (slot_valid i) (fun h => hia (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])
      · have hs := slot_ne (slot_valid b) (slot_valid i) (fun h => hib (offset_inj h))
        exact sub_disj (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk']) (by simp only [offset]; omega_using [hfit, i.isLt, a.isLt, b.isLt, hk'])
          (by omega_using [hs, hk'])

theorem swapsEnv_step (pairs : List (Slot × Slot)) (a b : Slot) (sw : Bool)
    {e f g : Env} (h : f = swapEnv a b sw e) (k : g = swapsEnv pairs sw f) :
    g = swapsEnv ((a, b) :: pairs) sw e := by
  rw [k, h]; rfl

theorem swapFields_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (pairs : List (Slot × Slot)) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    (sw : Bool) (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block (swapFields pairs)) s fun t =>
      FieldKeep x s t ∧ t.gpr .ecx = s.gpr .ecx ∧ env t.mem x = swapsEnv pairs sw (env s.mem x) := by
  induction pairs generalizing s with
  | nil => exact WP.block_nil ⟨FieldKeep.refl _ _, rfl, rfl⟩
  | cons pair pairs ih =>
    rcases pair with ⟨a, b⟩
    rw [swapFields, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (swapField_ok hc a b (hpairs _ List.mem_cons_self) sw hm) fun t ⟨kt, mt, et⟩ => ?_
    refine WP.mono (ih (kt.ctx hc) (fun p hp => hpairs p (List.mem_cons_of_mem _ hp)) (mt.trans hm))
      fun u ⟨ku, mu, eu⟩ => ?_
    exact ⟨kt.trans ku, mu.trans mt, swapsEnv_step pairs a b sw et eu⟩

theorem pointSelect_eval (e : Env) (sw : Bool) :
    point (swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e) 0 1 2 3 =
      if sw then point e 17 18 19 20 else point e 0 1 2 3 := by
  cases sw <;> rfl

theorem pointSelect_high (e : Env) (sw : Bool) :
    swapsEnv [(0, 17), (1, 18), (2, 19), (3, 20)] sw e 16 = e 16 := rfl

theorem pointSelect_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (sw : Bool)
    (hm : s.gpr .ecx = mask sw.toNat) :
    WP isa (.block pointSelect) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 =
        (if sw then point (env s.mem x) 17 18 19 20 else point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = env s.mem x 16 := by
  refine WP.mono (swapFields_ok hc _ (by decide) sw hm) fun t ⟨hk, _, he⟩ => ?_
  rw [he]
  exact ⟨hk, pointSelect_eval _ _, pointSelect_high _ _⟩

end VG.Proof.Ed25519.X86
