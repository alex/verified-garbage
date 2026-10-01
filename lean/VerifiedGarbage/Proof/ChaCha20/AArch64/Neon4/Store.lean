import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 16, s'.v (vreg k) = s.v (vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : StoreSame s₀ s₁) (h' : StoreSame s₁ s₂) :
    StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem xorRow_ok (s : State) (r j : Fin 4)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (xorRow r j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 ^^^
          s.v (vreg (rowWord r j))) ∧ StoreSame s s' := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 :=
    by obtain ⟨q, hq, hc⟩ := hout; exact ⟨q, List.mem_append_right _ hq, hc⟩
  have ha : (64 * j.val + 16 * r.val) % 16 = 0 ∧ 64 * j.val + 16 * r.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [xorRow, runBlock_cons, runBlock_nil, exec, addr, ha, and_self, ite_true, State.load, hin,
    Option.bind_some, Option.map_some, isa, runStep_some, RegUpd.gpr_setV, RegUpd.v_setV,
    vreg_ne, ite_false, VOp.eval, State.store,
    RegUpd.wr_setV, hout, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro k; simp only [RegUpd.v_setV, vreg_ne, ite_false]

/-- A byte of a 16-byte vector load. -/
theorem byte_read16 (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (m.read p 16).extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), show (8 * i + b) / 8 = i by omega,
    show (8 * i + b) % 8 = b by omega]

theorem xor_write_byte (m : Mem) (p : Addr) (v : BitVec 128) {i : Nat} (hi : i < 16) :
    (m.write p 16 (m.read p 16 ^^^ v)) (p + BitVec.ofNat 64 i) =
      m (p + BitVec.ofNat 64 i) ^^^ v.extractLsb' (8 * i) 8 := by
  simp only [Mem.write, Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), hi, ite_true,
    BitVec.extractLsb'_xor, byte_read16 m p hi]

theorem xor_write_apply (m : Mem) (p : Addr) (v : BitVec 128) (x : Addr) :
    (m.write p 16 (m.read p 16 ^^^ v)) x =
      if (x - p).toNat < 16 then m x ^^^ v.extractLsb' (8 * (x - p).toNat) 8 else m x := by
  by_cases h : (x - p).toNat < 16
  · simp only [Mem.write, h, ite_true, BitVec.extractLsb'_xor, byte_read16 m p h]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm p (x - p), BitVec.sub_add_cancel]
  · rw [ite_eq_right h]; exact Mem.write_apply h

/-- A sequence of distinct, aligned vector stores, tracked by their 16-byte slot. -/
def Data (m₀ m : Mem) (p : Addr) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < 256
    then m₀ x ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem Data.nil (m : Mem) (p : Addr) (out : Nat → BitVec 128) : Data m m p out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem Data.store {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) {n : Nat} (hn : n < 16) (hfresh : n ∉ done) :
    Data m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (p + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) p out (n :: done) := by
  intro x
  rw [xor_write_apply]
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  rw [h x]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < 256
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [hd, and_self, ite_true, he, hfresh, false_and, ite_false, hs,
      List.mem_cons_self, hb]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd]
    by_cases hb : (x - p).toNat < 256
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

def slot (r j : Fin 4) : Nat := 4 * j.val + r.val

theorem slot_lt (r j : Fin 4) : slot r j < 16 := by unfold slot; omega

theorem slot_inj (r i j : Fin 4) : slot r i = slot r j ↔ i = j := by
  simp only [slot, Fin.ext_iff]; omega

theorem xorList_ok (r : Fin 4) (js : List (Fin 4)) (hn : js.Nodup)
    {m₀ : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : Data m₀ s.mem p out done) (hp : s.gpr .x1 = p)
    (hv : ∀ j : Fin 4, s.v (vreg (rowWord r j)) = out (slot r j))
    (hfresh : ∀ j ∈ js, slot r j ∉ done)
    (hout : ∀ j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (js.flatMap (xorRow r))) s fun s' =>
      Data m₀ s'.mem p out (js.map (slot r) ++ done) ∧ StoreSame s s' := by
  induction js generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    have ho : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
      rw [hp]; exact hout j
    apply WP.block_append
    refine (xorRow_ok s r j ho).mono fun s' ⟨hm, hs⟩ => ?_
    have hd' : Data m₀ s'.mem p out (slot r j :: done) := by
      rw [hm, hp, hv j, show 64 * j.val + 16 * r.val = 16 * slot r j by unfold slot; omega]
      exact hd.store (slot_lt r j) (hfresh j (List.mem_cons_self ..))
    have hp' : s'.gpr .x1 = p := by rw [hs.gpr, hp]
    have hv' : ∀ i : Fin 4, s'.v (vreg (rowWord r i)) = out (slot r i) := by
      intro i; rw [hs.v, hv]
    have hfresh' : ∀ i ∈ js, slot r i ∉ slot r j :: done := by
      intro i hi
      simp only [List.mem_cons, slot_inj, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 (e ▸ hi),
        hfresh i (List.mem_cons_of_mem _ hi)⟩
    have hout' : ∀ i : Fin 4, InRegions s'.wr (p + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
      intro i; rw [hs.wr]; exact hout i
    refine (ih (List.nodup_cons.mp hn).2 hd' hp' hv' hfresh' hout').mono fun s'' ⟨hd'', ht⟩ =>
      ⟨?_, hs.trans ht⟩
    intro x
    simpa only [Data, List.map_cons, List.mem_append, List.mem_cons, or_assoc,
      or_left_comm] using hd'' x

end VG.Proof.ChaCha20.AArch64.Neon4
