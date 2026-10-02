import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Setup

/-! Feed the original input into the six row-oriented round results. -/
namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word)

theorem addRow_ok (s : State) (k : Fin 24)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block (addRow k)) s fun u =>
      (∀ j, j < 4 → vword (u.v (vreg k)) j = vword (s.v (vreg k)) j + input s k j) ∧
      (∀ r, r ≠ vreg k → r ≠ .v31 → u.v r = s.v r) ∧ LoadSame s u := by
  apply WP.block_append
  refine (inputRowInto_ok s k .v31 hin hctr).mono fun a ⟨hw,hv,hs⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runBlock_nil,exec,VOp.eval,isa,runStep_some,
    Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨fun j hj => ?_,fun r hr h31 => ?_,?_,hs.mem,hs.rd,hs.wr,hs.sp⟩
  · rw [RegUpd.v_setV_self,vword_map2 _ _ _ hj,hv _ (vreg_ne k),hw j hj]
  · rw [RegUpd.v_setV_of_ne _ _ hr,hv r h31]
  · intro r hr
    exact hs.gpr r hr

structure Added (s₀ : State) (done : List (Fin 24)) (s : State) : Prop where
  words : ∀ k : Fin 24, ∀ j, j < 4 → vword (s.v (vreg k)) j =
    vword (s₀.v (vreg k)) j + if k ∈ done then input s₀ k j else 0
  same : LoadSame s₀ s

theorem addList_ok (ks : List (Fin 24)) (hn : ks.Nodup) {s₀ s : State} {done : List (Fin 24)}
    (h : Added s₀ done s) (hf : ∀ k ∈ ks, k ∉ done)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (ks.flatMap addRow)) s (Added s₀ (ks ++ done)) := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil h
  | cons k ks ih =>
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
      rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
    have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
      rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
    apply WP.block_append
    refine (addRow_ok s k hi hc).mono fun a ⟨hw,hv,hs⟩ => ?_
    have h' : Added s₀ (k :: done) a := by
      refine ⟨fun l j hj => ?_,h.same.trans hs⟩
      by_cases he : l = k
      · subst l
        rw [hw j hj,h.words k j hj,input_same h.same]
        simp [hf k (List.mem_cons_self ..)]
      · rw [hv _ (fun e => he ((vreg_inj l k).mp e)) (vreg_ne l),h.words l j hj]
        simp only [List.mem_cons,he,false_or]
    have hf' : ∀ l ∈ ks, l ∉ k :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hl),hf l (List.mem_cons_of_mem _ hl)⟩
    refine (ih (List.nodup_cons.mp hn).2 h' hf').mono fun u hu => ?_
    refine ⟨fun l j hj => ?_,hu.same⟩
    simpa only [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu.words l j hj

theorem feedForward_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block feedForward) s fun u =>
      (∀ k : Fin 24, ∀ j, j < 4 → vword (u.v (vreg k)) j =
        vword (s.v (vreg k)) j + input s k j) ∧ LoadSame s u := by
  refine (addList_ok (List.finRange 24) (List.nodup_finRange 24) (done := [])
    ⟨(fun _ _ _ => by simp),VG.Proof.ChaCha20.AArch64.Neon4.LoadSame.refl s⟩
    (fun _ _ h => by cases h) hin hctr).mono fun u hu => ⟨?_,hu.same⟩
  intro k j hj
  simpa only [List.append_nil,List.mem_finRange,ite_true] using hu.words k j hj
end VG.Proof.ChaCha20.AArch64.Rows6
