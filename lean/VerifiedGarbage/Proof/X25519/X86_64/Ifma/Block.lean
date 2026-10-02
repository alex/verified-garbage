import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound

/-!
# X25519 on x86-64 with AVX512_IFMA: what a block leaves in memory

After a block whose stores (`Sym.st`) are 32-byte slots apart, each quadword
of a slot it stored is its term, and every quadword it did not store is as
before.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64

/-- The quadword at `base + d`. -/
def mq (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (base + BitVec.ofNat 64 d) 64

theorem val_extract (s₀ : State) (t : T) {l : Nat} (hl : l < 4) :
    (t.val s₀).extractLsb' (8 * (8 * l)) (8 * 8) = t.eval s₀ l := by
  have := VG.Proof.Poly1305.X86_64.Avx2.qword256_cat (t.eval s₀ 3) (t.eval s₀ 2) (t.eval s₀ 1)
    (t.eval s₀ 0) hl
  rw [show 8 * (8 * l) = 64 * l by omega]
  refine this.trans ?_
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- A quadword no store touched. -/
theorem stores_mq_fresh (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × T)) {d : Nat}, d < 2 ^ 62 → (∀ e ∈ st, e.1 < 2 ^ 62) →
      (st.all fun (e, _) => d + 8 ≤ e || e + 32 ≤ d) = true →
      mq (stores s₀ base st m) base d = mq m base d
  | [], _, _, _, _ => rfl
  | (e, t) :: st, d, hd, he, hf => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
    have e1 := readW_writeW_off (stores s₀ base st m) base (t.val s₀) (d := d) (e := e) (n := 8)
      (by omega) (by have := he _ (List.mem_cons_self ..); simp at this; omega) (by omega)
    have e2 := stores_mq_fresh s₀ base m st hd (fun x hx => he x (List.mem_cons_of_mem _ hx)) hf.2
    exact e1.trans e2

/-- Slots 32 bytes apart. -/
def Apart (st : List (Nat × T)) : Prop := st.Pairwise fun x y => x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1

instance (st : List (Nat × T)) : Decidable (Apart st) := by unfold Apart; infer_instance

/-- A quadword of a stored slot. -/
theorem stores_mq (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × T)) {e : Nat} {t : T} {l : Nat}, (e, t) ∈ st → l < 4 →
      (∀ x ∈ st, x.1 < 2 ^ 62) → Apart st → mq (stores s₀ base st m) base (e + 8 * l) = t.eval s₀ l
  | [], _, _, _, h, _, _, _ => by cases h
  | (e₀, t₀) :: st, e, t, l, h, hl, hs, ha => by
    simp only [Apart, List.pairwise_cons] at ha
    simp only [stores]
    rcases List.mem_cons.1 h with h | h
    · cases h
      rw [mq, BitVec.ofNat_add, ← BitVec.add_assoc,
        readW_writeW_inside _ _ _ (k := 8 * l) (n := 8) (by omega) (by decide), val_extract _ _ hl]
    · have h₀ := ha.1 _ h
      have e1 := readW_writeW_off (stores s₀ base st m) base (t₀.val s₀) (d := e + 8 * l) (e := e₀) (n := 8)
        (by have := hs _ (List.mem_cons_of_mem _ h); simp at this; omega)
        (by have := hs _ (List.mem_cons_self ..); simp at this; omega)
        (by simp at h₀; omega)
      exact e1.trans (stores_mq s₀ base m st h hl (fun x hx => hs x (List.mem_cons_of_mem _ hx)) ha.2)

end VG.Proof.X25519.X86_64.Ifma
