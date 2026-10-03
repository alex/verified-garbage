import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Add

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6

/-- Add a common state row without rereading it for each block. -/
theorem cachedAdd_ok {s₀ s : State} {done : List (Fin 24)} (h : Added s₀ done s)
    (k : Fin 24) (hk : k ∉ done)
    (hc : ∀ j, j < 4 → vword (s.v .v31) j = input s₀ k j) :
    WP isa (.block [.vop (.add .s4 (vreg k) (vreg k) .v31)]) s fun u =>
      Added s₀ (k :: done) u ∧ u.v .v31 = s.v .v31 := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runBlock_nil,exec,VOp.eval,isa,runStep_some,
    Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun l j hj => ?_,⟨h.same.gpr,h.same.mem,h.same.rd,h.same.wr,h.same.sp⟩⟩,?_⟩
  · by_cases he : l = k
    · subst l
      rw [RegUpd.v_setV_self,vword_map2 _ _ _ hj,h.words k j hj,hc j hj]
      simp only [hk,ite_false,List.mem_cons_self,ite_true]
      exact congrArg (fun x => x + input s₀ k j) (BitVec.add_zero _)
    · rw [RegUpd.v_setV_of_ne _ _ (fun e => he ((vreg_inj l k).mp e)),h.words l j hj]
      simp only [List.mem_cons,he,false_or]
  · exact RegUpd.v_setV_of_ne _ _ (Ne.symm (vreg_ne k))

theorem cachedAdds_ok (ks : List (Fin 24)) (hn : ks.Nodup) {s₀ s : State}
    {done : List (Fin 24)} (h : Added s₀ done s) (hf : ∀ k ∈ ks, k ∉ done)
    (hc : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v .v31) j = input s₀ k j) :
    WP isa (.block (ks.map fun k => Instr.vop (.add .s4 (vreg k) (vreg k) .v31))) s
      (Added s₀ (ks ++ done)) := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil h
  | cons k ks ih =>
    change WP isa (.block (([Instr.vop (.add .s4 (vreg k) (vreg k) .v31)] : List Instr) ++
      ks.map fun k => Instr.vop (.add .s4 (vreg k) (vreg k) .v31))) s _
    apply WP.block_append
    refine (cachedAdd_ok h k (hf _ (List.mem_cons_self ..))
      (hc _ (List.mem_cons_self ..))).mono
      fun a ⟨ha,hcache⟩ => ?_
    refine (ih (List.nodup_cons.mp hn).2 ha (fun l hl => ?_)
      (fun l hl j hj => by rw [hcache]; exact hc l (List.mem_cons_of_mem _ hl) j hj)).mono
      fun u hu => ?_
    · simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hl),hf l (List.mem_cons_of_mem _ hl)⟩
    · refine ⟨fun l j hj => ?_,hu.same⟩
      simpa only [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu.words l j hj

def rowKeys (r : Fin 4) : List (Fin 24) := (List.finRange 6).map (fun b => row b r)

theorem rowKeys_nodup (r : Fin 4) : (rowKeys r).Nodup := by
  exact (by decide +kernel : ∀ r : Fin 4, (rowKeys r).Nodup) r

theorem rowKeys_mod (r : Fin 4) (k : Fin 24) (hk : k ∈ rowKeys r) : k.val % 4 = r.val := by
  exact (by decide +kernel : ∀ r : Fin 4, ∀ k : Fin 24, k ∈ rowKeys r → k.val % 4 = r.val) r k hk

theorem cachedFeedRow_ok (r : Fin 3) {s₀ s : State} {done : List (Fin 24)}
    (h : Added s₀ done s) (hf : ∀ k ∈ rowKeys ⟨r.val, by omega⟩, k ∉ done)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (cachedFeedRow r)) s (Added s₀ (rowKeys ⟨r.val, by omega⟩ ++ done)) := by
  let k : Fin 24 := ⟨r.val, by omega⟩
  have hm : k.val % 4 = r.val := Nat.mod_eq_of_lt (by change r.val < 4; omega)
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
  have he : cachedFeedRow r = inputRowInto k .v31 ++
      ((rowKeys ⟨r.val, by omega⟩).map fun l => Instr.vop (.add .s4 (vreg l) (vreg l) .v31)) := by
    simp only [cachedFeedRow,inputRowInto,hm,show ¬r.val = 3 by omega,ite_false,
      List.append_nil,rowKeys,List.map_map]
    rfl
  rw [he]
  apply WP.block_append
  refine (inputRowInto_ok s k .v31 hi hc).mono fun a ⟨hw,hv,hs⟩ => ?_
  have ha : Added s₀ done a := ⟨fun l j hj => by rw [hv _ (vreg_ne l)]; exact h.words l j hj,
    h.same.trans hs⟩
  refine cachedAdds_ok _ (rowKeys_nodup _) ha hf ?_
  intro l hl j hj
  rw [hw j hj,input_same h.same]
  simp only [input,hm,rowKeys_mod _ l hl,show ¬(r.val = 3 ∧ j = 0) by omega,ite_false]

theorem feedForward_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block feedForward) s fun u =>
      (∀ k : Fin 24, ∀ j, j < 4 → vword (u.v (vreg k)) j =
        vword (s.v (vreg k)) j + input s k j) ∧ LoadSame s u := by
  have h : Added s [] s := ⟨fun _ _ _ => by simp,
    VG.Proof.ChaCha20.AArch64.Neon4.LoadSame.refl s⟩
  unfold feedForward
  rw [List.append_assoc,List.append_assoc]
  apply WP.block_append
  refine (cachedFeedRow_ok 0 h (fun _ _ h => by cases h) hin hctr).mono fun a ha => ?_
  apply WP.block_append
  refine (cachedFeedRow_ok 1 ha (by decide +kernel) hin hctr).mono fun b hb => ?_
  apply WP.block_append
  refine (cachedFeedRow_ok 2 hb (by decide +kernel) hin hctr).mono fun c hc => ?_
  change WP isa (.block ((rowKeys 3).flatMap addRow)) c _
  refine (addList_ok (rowKeys 3) (rowKeys_nodup 3) hc (by decide +kernel) hin hctr).mono
    fun u hu => ⟨?_,hu.same⟩
  intro k j hj
  have hall : k ∈ rowKeys 3 ++ (rowKeys 2 ++ (rowKeys 1 ++ (rowKeys 0 ++ []))) := by
    exact (by decide +kernel : ∀ k : Fin 24,
      k ∈ rowKeys 3 ++ (rowKeys 2 ++ (rowKeys 1 ++ (rowKeys 0 ++ [])))) k
  have hw := hu.words k j hj
  change vword (u.v (vreg k)) j = vword (s.v (vreg k)) j +
    if k ∈ rowKeys 3 ++ (rowKeys 2 ++ (rowKeys 1 ++ (rowKeys 0 ++ []))) then input s k j else 0 at hw
  simpa only [hall,ite_true] using hw

end VG.Proof.ChaCha20.AArch64.Rows6
