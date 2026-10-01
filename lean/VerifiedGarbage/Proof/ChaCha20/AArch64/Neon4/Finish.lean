import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- One 16-byte row of the final four ChaCha blocks. -/
def output (vs : Nat → CState) (n : Nat) : BitVec 128 :=
  ofVWords ((vs (n / 4))[4 * (n % 4)]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 1]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 2]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 3]'(by omega))

theorem output_slot (vs : Nat → CState) (r j : Fin 4) :
    output vs (slot r j) = ofVWords ((vs j)[rowWord r 0]) ((vs j)[rowWord r 1])
      ((vs j)[rowWord r 2]) ((vs j)[rowWord r 3]) := by
  have hd : slot r j / 4 = j.val := by unfold slot; omega
  have hm : slot r j % 4 = r.val := by unfold slot; omega
  simp only [output, hd, hm, rowWord, Fin.getElem_fin]; rfl

structure Keep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.trans {s₀ s₁ s₂ : State} (h : Keep s₀ s₁) (h' : Keep s₁ s₂) : Keep s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

def rowSlots (r : Fin 4) : List Nat := (List.finRange 4).map (slot r)

theorem finishRowFor_ok (js : List (Fin 4)) (hj : js.Nodup) {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (r : Fin 4) (hd : Data m₀ s.mem p (output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ j ∈ js, slot r j ∉ done)
    (hout : ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRowFor js r)) s fun s' =>
      Data m₀ s'.mem p (output vs) (js.map (slot r) ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (vreg k) = s.v (vreg k)) ∧ Keep s s' := by
  apply WP.block_append
  refine (transpose_ok s r).mono fun t ⟨ht, ho, hs⟩ => ?_
  have hd' : Data m₀ t.mem p (output vs) done := hs.mem ▸ hd
  have hp' : t.gpr .x1 = p := by rw [hs.gpr, hp]
  have hv' : ∀ j : Fin 4, t.v (vreg (rowWord r j)) = output vs (slot r j) := by
    intro j; rw [ht j, transposed, output_slot, hv 0 j, hv 1 j, hv 2 j, hv 3 j]
  have hout' : ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro j hjs; rw [hs.wr]; exact hout j hjs
  refine (xorList_ok r js hj hd' hp' hv'
    hfresh hout').mono fun u ⟨hu, hk⟩ => ⟨hu, ?_, ?_⟩
  · intro k hkr; rw [hk.v, ho k hkr]
  · exact ⟨hk.gpr.trans hs.gpr, hk.rd.trans hs.rd, hk.wr.trans hs.wr, hk.sp.trans hs.sp⟩

theorem slot_ne {r t : Fin 4} (hne : r ≠ t) (i j : Fin 4) : slot r i ≠ slot t j := by
  intro e; apply hne; apply Fin.ext; unfold slot at e; omega

theorem finishRowsFor_ok (js : List (Fin 4)) (hj : js.Nodup) (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (hd : Data m₀ s.mem p (output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ r ∈ rs, ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ r ∈ rs, ∀ j ∈ js, slot r j ∉ done)
    (hout : ∀ r : Fin 4, ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap (finishRowFor js))) s fun s' =>
      Data m₀ s'.mem p (output vs) (rs.flatMap (fun r => js.map (slot r)) ++ done) ∧ Keep s s' := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, rfl, rfl, rfl⟩
  | cons r rs ih =>
    have hr := (List.nodup_cons.mp hn).1
    apply WP.block_append
    refine (finishRowFor_ok js hj r hd hp (hv r (List.mem_cons_self ..))
      (hfresh r (List.mem_cons_self ..)) (hout r)).mono fun t ⟨ht, hvkeep, hs⟩ => ?_
    have hp' : t.gpr .x1 = p := by rw [hs.gpr, hp]
    have hv' : ∀ q ∈ rs, ∀ i j : Fin 4,
        vword (t.v (vreg (rowWord q i))) j = (vs j)[rowWord q i] := by
      intro q hq i j
      have hqr : (rowWord q i).val / 4 ≠ r.val := by
        have hqr : q ≠ r := fun e => hr (e ▸ hq)
        simp only [rowWord] at *; omega
      rw [hvkeep _ hqr]; exact hv q (List.mem_cons_of_mem _ hq) i j
    have hfresh' : ∀ q ∈ rs, ∀ j ∈ js, slot q j ∉ js.map (slot r) ++ done := by
      intro q hq j hjs
      simp only [List.mem_append, not_or]
      refine ⟨?_, hfresh q (List.mem_cons_of_mem _ hq) j hjs⟩
      intro hm
      obtain ⟨i, _, he⟩ := List.mem_map.mp hm
      exact slot_ne (fun (e : q = r) => hr (e ▸ hq)) j i he.symm
    have hout' : ∀ q : Fin 4, ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * q)) 16 := by
      intro q j hjs; rw [hs.wr]; exact hout q j hjs
    refine (ih (List.nodup_cons.mp hn).2 ht hp' hv' hfresh' hout').mono fun u ⟨hu, hk⟩ =>
      ⟨?_, hs.trans hk⟩
    intro x
    simpa only [Data, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hu x

theorem finishRow_ok {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (r : Fin 4) (hd : Data m₀ s.mem p (output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ j : Fin 4, slot r j ∉ done)
    (hout : ∀ j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRow r)) s fun s' =>
      Data m₀ s'.mem p (output vs) (rowSlots r ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (vreg k) = s.v (vreg k)) ∧ Keep s s' := by
  exact finishRowFor_ok (List.finRange 4) (List.nodup_finRange 4) r hd hp hv
    (fun j _ => hfresh j) (fun j _ => hout j)

theorem finishRows_ok (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (hd : Data m₀ s.mem p (output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ r ∈ rs, ∀ i j : Fin 4, vword (s.v (vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ r ∈ rs, ∀ j : Fin 4, slot r j ∉ done)
    (hout : ∀ r j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap finishRow)) s fun s' =>
      Data m₀ s'.mem p (output vs) (rs.flatMap rowSlots ++ done) ∧ Keep s s' := by
  exact finishRowsFor_ok (List.finRange 4) (List.nodup_finRange 4) rs hn hd hp hv
    (fun r hr j _ => hfresh r hr j) (fun r j _ => hout r j)

theorem all_slots (n : Fin 16) : n.val ∈ (List.finRange 4).flatMap rowSlots :=
  (show ∀ n : Fin 16, n.val ∈ (List.finRange 4).flatMap rowSlots by decide) n

theorem output_word (vs : Nat → CState) (n : Nat) {e : Nat} (he : e < 4) :
    vword (output vs n) e = (vs (n / 4))[4 * (n % 4) + e]'(by omega) := by
  rw [output, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem byte_vword (v : BitVec 128) {i : Nat} (_hi : i < 16) :
    v.extractLsb' (8 * i) 8 = (vword v (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * (i % 4) + b < 32 by omega]
  exact congrArg v.getLsbD (by omega)

theorem output_byte (vs : Nat → CState) {k : Nat} (_hk : k < 256) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [byte_vword _ (by omega), output_word _ _ (by omega),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show k / 16 / 4 = k / 64 by omega,
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega,
    show k % 16 % 4 = k % 64 % 4 by omega]

theorem Data.frame {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) : Frame [⟨p, 256⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 256 := by
    have hh := hx ⟨p, 256⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x, ite_eq_right (fun h => hn h.2)]

theorem finishBlocks_ok {s : State} {vs : Nat → CState} (h : Holds vs s)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap finishRow)) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 256⟩] s.mem s'.mem ∧ Keep s s' := by
  refine (finishRows_ok (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output vs)) rfl (fun r _ i j => h (rowWord r i) j j.isLt)
    (fun _ _ _ => List.not_mem_nil) hout).mono fun s' ⟨hd, hs⟩ => ⟨?_, hd.frame, hs⟩
  intro k hk
  rw [hd _, Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),
    ite_eq_left ⟨List.mem_append_left _ (all_slots ⟨k / 16, by omega⟩), hk⟩,
    output_byte vs hk]

end VG.Proof.ChaCha20.AArch64.Neon4
