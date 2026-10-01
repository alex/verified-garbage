import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

theorem addWord_ok (s : State) (k : Fin 16)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (addWord k)) s fun s' =>
      (∀ j, j < 4 → vword (s'.v (vreg k)) j = vword (s.v (vreg k)) j + input s k j) ∧
      (∀ l : Fin 16, l ≠ k → s'.v (vreg l) = s.v (vreg l)) ∧ LoadSame s s' := by
  apply WP.block_append
  refine (inputWord_ok s k hin).mono fun s' ⟨hw, hv, hs⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, hs.gpr, hs.mem, hs.rd, hs.wr, hs.sp⟩
  · intro j hj
    rw [RegUpd.v_setV_self, vword_map2 _ _ _ hj, hv _ (vreg_ne k), hw j hj]
  · intro l hl
    rw [RegUpd.v_setV, ite_eq_right (fun e => hl ((vreg_inj l k).mp e)), hv _ (vreg_ne l)]

theorem feedList_ok (ks : List (Fin 16)) (hn : ks.Nodup) (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (ks.flatMap addWord)) s fun s' =>
      (∀ k : Fin 16, ∀ j, j < 4 → vword (s'.v (vreg k)) j =
        if k ∈ ks then vword (s.v (vreg k)) j + input s k j else vword (s.v (vreg k)) j) ∧
      LoadSame s s' := by
  induction ks generalizing s with
  | nil => exact WP.block_nil ⟨fun _ _ _ => rfl, LoadSame.refl s⟩
  | cons k ks ih =>
    obtain ⟨hk, hn⟩ := List.nodup_cons.mp hn
    apply WP.block_append
    refine (addWord_ok s k (hin k)).mono fun s' ⟨hw, hv, hs⟩ => ?_
    have hi : ∀ l : Fin 16, InRegions (s'.rd ++ s'.wr) (s'.gpr .x0 + BitVec.ofNat 64 (4 * l)) 4 := by
      intro l; rw [hs.rd, hs.wr, hs.gpr _ (by decide)]; exact hin l
    refine (ih hn s' hi).mono fun s'' ⟨ht, hsame⟩ => ⟨?_, hs.trans hsame⟩
    intro l j hj
    rw [ht l j hj, input_same hs]
    by_cases e : l = k
    · subst l; simp only [hk, ite_false, hw j hj, List.mem_cons_self, ite_true]
    · rw [hv l e]
      simp only [List.mem_cons, e, false_or]

theorem feed_ok {s : State} {vs : Nat → CState} (h : Holds vs s)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block ((List.finRange 16).flatMap addWord)) s fun s' =>
      (∀ k : Fin 16, ∀ j, j < 4 → vword (s'.v (vreg k)) j = (vs j)[k] + input s k j) ∧
      LoadSame s s' := by
  refine (feedList_ok _ (List.nodup_finRange 16) s hin).mono fun s' ⟨hw, hs⟩ => ⟨?_, hs⟩
  intro k j hj
  rw [hw k j hj, ite_eq_left (List.mem_finRange k), h k j hj]

end VG.Proof.ChaCha20.AArch64.Neon4
