import VerifiedGarbage.Proof.Argon2.X86.Derive.Body

/-!
# Argon2 on x86 (32-bit): the derivation's locals

`lw s₀ s d`: the word at `[ebp + d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

/-- The word at `[ebp + d]`. -/
abbrev lw (s₀ s : State) (d : Nat) : BitVec 32 := s.mem.readW (addr (E s₀) d) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 236) :
    (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d := add_nat (by have := E_hi hp; omega)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 236) (he : e + 4 ≤ 236) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (addr (E s₀) d) v).readW (addr (E s₀) e) 32 = m.readW (addr (E s₀) e) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := E_hi hp; omega) (by have := E_hi hp; omega) hde.symm

theorem Inv.store_loc {s t : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (addr (E s₀) d) v)) :
    Inv s₀ t ∧ lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  have hE := E_hi hp
  refine ⟨h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := locR s₀) (by simp) v
      (contains32 (by rw [loc_addr hp (by omega)]; omega) (by rw [loc_addr hp (by omega)]; omega))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, lw_store hp (by omega) he hde]

/-- `mov [ebp + d], r` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (addr (E s₀) d) (s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebp, d⟩ r :: is)) s Q :=
  VG.X86.Wp.wp_stm h.ebp (loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `mov r, [ebp + d]` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, d⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (loc_in' hp h hd) k

/-- `mov r, [ebp + argOff i]` -/
theorem wp_ldarg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, Impl.Argon2.X86.Derive.argOff i⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (h.arg_in hp hi) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Disjoint ⟨addr (E s₀) d, 4⟩ r := by
  have hE := E_hi hp
  have hl := hp.esp_lo
  have hEn := E_nat hp
  have sub := loc_stk hp (d := d) (n := 4) hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact disj32 (.inr (by rw [sub_nat (by rw [E_nat hp]; omega), loc_addr hp (by omega)]; omega))
      (by rw [loc_addr hp (by omega)]; omega) (by rw [sub_nat (by rw [E_nat hp]; omega)]; omega)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `ebp` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = (entry s₀).mem → (∀ r, r ≠ .ebp → t.gpr r = (entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.mov .ebp (.reg .esp) :: is)) (entry s₀) Q :=
  VG.X86.Wp.wp_mov fun t u => k t
    ⟨by rw [u.other _ (by decide), entry_esp], by rw [u.gpr, entry_esp], by rw [u.rd, entry_rd],
      by rw [u.wr], by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.X86.Derive
