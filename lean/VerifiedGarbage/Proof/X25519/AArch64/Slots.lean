import VerifiedGarbage.Proof.X25519.AArch64.Limbwise

/-!
# X25519 on AArch64: the field elements in their slots

Untrusted: everything here is checked by Lean. The elements live in the
slots of the working space (`slot n`, `n < 15`); `Inv b s₀ s vals bnds` says
that each slot `n` with a bound `bnds n = some k` stands for the field
element `vals n` with limbs below `2^k`, and that since `s₀` only the
registers of the field operations and the slots have changed. Each field
operation updates `vals` and `bnds` at its result's slot.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-- The limbs `f` stand for `x`, and are below `2^k`. -/
def Rep (f : Nat → Nat) (x : Fe) (k : Nat) : Prop := Bnd f k ∧ toFe (val15 f) = x

/-- Every slot with a bound stands for its value. -/
def Sl (m : Mem) (b : Addr) (vals : Nat → Fe) (bnds : Nat → Option Nat) : Prop :=
  ∀ n < 15, ∀ k, bnds n = some k → Rep (limbs m b (slot n)) (vals n) k

/-- The area of the slots. -/
abbrev slotArea (b : Addr) : Region := ⟨b + BitVec.ofNat 64 64, 1920⟩

/-- Between the field operations. -/
structure Inv (b : Addr) (s₀ s : State) (vals : Nat → Fe) (bnds : Nat → Option Nat) : Prop where
  sc : Sc b s
  sl : Sl s.mem b vals bnds
  kp : Kp fieldRegs s₀ s
  fr : Frame [slotArea b] s₀.mem s.mem

theorem slot_ok {n : Nat} (hn : n < 15) : Slot (slot n) := by
  simp only [Slot, slot]; omega

theorem slot_alias (o a : Nat) : Alias (slot o) (slot a) := by
  simp only [Alias, slot]; omega

theorem slotR_sub (b : Addr) {n : Nat} (hn : n < 15) : Region.Sub (slotR b (slot n)) (slotArea b) :=
  Offset.sub b (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem slotR_disjoint (b : Addr) {n n' : Nat} (hn : n < 15) (hn' : n' < 15) (h : n ≠ n') :
    (slotR b (slot n)).Disjoint (slotR b (slot n')) :=
  Offset.disjoint b (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

/-- The limbs of an element outside a frame's regions. -/
theorem limbs_frame {b : Addr} {o : Nat} (ho : Slot o) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (slotR b o).Disjoint r) : limbs m' b o = limbs m b o := funext fun i => by
  simp only [limbs]
  split
  · rename_i hi
    simp only [wd]
    rw [hf.readW (slot_contains b ho hi) hd (by decide)]
  · rfl

theorem frame_slot {b : Addr} {s₀ s s' : State} (hf : Frame [slotArea b] s₀.mem s.mem) {n : Nat}
    (hn : n < 15) (h : Frame [slotR b (slot n)] s.mem s'.mem) : Frame [slotArea b] s₀.mem s'.mem :=
  hf.trans (h.sub fun r hr => ⟨slotArea b, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact slotR_sub b hn⟩)

theorem limbs_other {b : Addr} {s s' : State} {o n : Nat} (ho : o < 15) (hn : n < 15) (h : n ≠ o)
    (hf : Frame [slotR b (slot o)] s.mem s'.mem) : limbs s'.mem b (slot n) = limbs s.mem b (slot n) :=
  limbs_frame (slot_ok hn) hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact slotR_disjoint b hn ho h

/-- A slot updated with a new value and bound. -/
theorem Sl.update {m m' : Mem} {b : Addr} {vals : Nat → Fe} {bnds : Nat → Option Nat} (h : Sl m b vals bnds)
    {o : Nat} (x : Fe) (k : Nat) (ho : Rep (limbs m' b (slot o)) x k)
    (hother : ∀ n < 15, n ≠ o → limbs m' b (slot n) = limbs m b (slot n)) :
    Sl m' b (Function.update vals o x) (Function.update bnds o (some k)) := by
  intro n hn j hj
  by_cases hno : n = o
  · subst hno
    rw [Function.update_self] at hj ⊢
    cases hj
    exact ho
  · rw [Function.update_of_ne hno] at hj ⊢
    rw [hother n hn hno]
    exact h n hn j hj

theorem Sl.bnd {m : Mem} {b : Addr} {vals : Nat → Fe} {bnds : Nat → Option Nat} (h : Sl m b vals bnds)
    {n k k' : Nat} (hn : n < 15) (hk : bnds n = some k) (hkk : k ≤ k') :
    Bnd (limbs m b (slot n)) k' ∧ toFe (val15 (limbs m b (slot n))) = vals n :=
  ⟨(h n hn k hk).1.mono hkk, (h n hn k hk).2⟩

theorem Inv.kp_sub {b : Addr} {s₀ s s' : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {W : List Reg} (k : Kp W s s') (hW : W ⊆ fieldRegs) : Kp fieldRegs s₀ s' :=
  (h.kp.trans (k.sub hW)).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩)

/-! ## The operations on slots -/

theorem mul_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 26) (hkc' : kc ≤ 26) :
    WP isa (.block (mul (slot o) (slot a) (slot c))) s fun s' =>
      Inv b s₀ s' (Function.update vals o (vals a * vals c)) (Function.update bnds o (some 18)) :=
  WP.mono (mul_ok h.sc (slot_ok ho) (slot_ok ha) (slot_ok hc)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := mulF_spec b1 b2
      rw [e]; exact ⟨r1, by rw [r2, v1, v2]⟩) fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (List.Subset.refl _), frame_slot h.fr ho f⟩

theorem mulSmall_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o a : Nat} (ho : o < 15) (ha : a < 15) {ka : Nat}
    (hka : bnds a = some ka) (hka' : ka ≤ 26) :
    WP isa (.block (mulSmall (slot o) (slot a))) s fun s' =>
      Inv b s₀ s' (Function.update vals o (a24 * vals a)) (Function.update bnds o (some 18)) :=
  WP.mono (mulSmall_ok h.sc (slot_ok ho) (slot_ok ha)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨r1, r2⟩ := mulSmallF_spec b1
      rw [e]; exact ⟨r1, by rw [r2, v1]⟩) fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (List.Subset.refl _), frame_slot h.fr ho f⟩

theorem add_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 25) (hkc' : kc ≤ 25) :
    WP isa (.block (add (slot o) (slot a) (slot c))) s fun s' =>
      Inv b s₀ s' (Function.update vals o (vals a + vals c)) (Function.update bnds o (some 26)) :=
  WP.mono (add_ok h.sc (slot_ok ho) (slot_ok ha) (slot_ok hc) (slot_alias o a) (slot_alias o c))
    fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := addF_spec b1 b2 (by decide) (Nat.le_refl _)
      rw [e]; exact ⟨r1, by rw [r2, v1, v2]⟩) fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (by decide), frame_slot h.fr ho f⟩

theorem sub_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 21) (hkc' : kc ≤ 20) :
    WP isa (.block (sub (slot o) (slot a) (slot c))) s fun s' =>
      Inv b s₀ s' (Function.update vals o (vals a - vals c)) (Function.update bnds o (some 26)) :=
  WP.mono (sub_ok h.sc (slot_ok ho) (slot_ok ha) (slot_ok hc) (slot_alias o a) (slot_alias o c))
    fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := subF_spec b1 b2 (Nat.le_refl _) (by decide)
      rw [e]; exact ⟨r1.mono (by decide), by rw [r2, v1, v2]⟩) fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (by decide), frame_slot h.fr ho f⟩

theorem copy_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {o a : Nat} (ho : o < 15) (ha : a < 15) {ka : Nat}
    (hka : bnds a = some ka) :
    WP isa (.block (copy (slot o) (slot a))) s fun s' =>
      Inv b s₀ s' (Function.update vals o (vals a)) (Function.update bnds o (some ka)) :=
  WP.mono (copy_ok h.sc (slot_ok ho) (slot_ok ha) (slot_alias o a)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by rw [e]; exact h.sl a ha ka hka)
      fun n hn hno => limbs_other ho hn hno f,
    h.kp_sub k (by decide), frame_slot h.fr ho f⟩

theorem cswap_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : Inv b s₀ s vals bnds) {x y : Nat} (hx : x < 15) (hy : y < 15) (hxy : x ≠ y) {k : Nat}
    (hkx : bnds x = some k) (hky : bnds y = some k) {sw : Nat} (hm : s.gpr .x22 = maskB (sw == 1)) :
    WP isa (.block (cswap (slot x) (slot y))) s fun s' =>
      Inv b s₀ s' (Function.update (Function.update vals x (cswap sw (vals x) (vals y)).1) y
        (cswap sw (vals x) (vals y)).2) bnds ∧ s'.gpr .x22 = s.gpr .x22 := by
  refine WP.mono (cswap_ok h.sc (slot_ok hx) (slot_ok hy) (by simp only [slot]; omega) hm)
    fun s' ⟨ex, ey, f, kp⟩ => ⟨⟨h.sc.of_kp kp (by decide), ?_, h.kp_sub kp (by decide), ?_⟩,
      kp.gpr _ (by decide)⟩
  · intro n hn j hj
    have rx := h.sl x hx k hkx
    have ry := h.sl y hy k hky
    have csw : ∀ a c : Fe, cswap sw a c = if (sw == 1) = true then (c, a) else (a, c) := fun a c => by
      simp only [Spec.X25519.cswap, beq_iff_eq]
    by_cases hny : n = y
    · subst hny
      rw [Function.update_self, ey, csw]
      have hjk : j = k := Option.some.inj (hj.symm.trans hky)
      subst hjk
      cases (sw == 1)
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact ry
      · rw [ite_eq_left rfl, ite_eq_left rfl]; exact rx
    · rw [Function.update_of_ne hny]
      by_cases hnx : n = x
      · subst hnx
        rw [Function.update_self, ex, csw]
        have hjk : j = k := Option.some.inj (hj.symm.trans hkx)
        subst hjk
        cases (sw == 1)
        · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact rx
        · rw [ite_eq_left rfl, ite_eq_left rfl]; exact ry
      · rw [Function.update_of_ne hnx]
        rw [limbs_frame (slot_ok hn) f fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact slotR_disjoint b hn hx hnx
          · exact slotR_disjoint b hn hy hny]
        exact h.sl n hn j hj
  · exact h.fr.trans (f.sub fun r hr => ⟨slotArea b, List.mem_singleton_self _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotR_sub b hx
      · exact slotR_sub b hy⟩)

end VG.Proof.X25519.AArch64
