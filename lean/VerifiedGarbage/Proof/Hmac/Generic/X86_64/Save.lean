import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Loops

/-!
# HMAC over any streaming hash function on x86-64: our caller's registers

Untrusted: everything here is checked by Lean. The six callee-saved
registers we use are stored in `scratch` after the working space of the
functions we call (`Hash.saved`), and loaded back at the end.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at ofInt_natCast contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_store wp_movm)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Hash)

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 48⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (slot H scr 0) 64 = s₀.gpr .rbx
  rbp : m.readW (slot H scr 1) 64 = s₀.gpr .rbp
  r12 : m.readW (slot H scr 2) 64 = s₀.gpr .r12
  r13 : m.readW (slot H scr 3) 64 = s₀.gpr .r13
  r14 : m.readW (slot H scr 4) 64 = s₀.gpr .r14
  r15 : m.readW (slot H scr 5) 64 = s₀.gpr .r15

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 6) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.Sha256.X86_64.sub_offset (by omega) (by omega)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (hij : i ≠ j) (hW : H.W ≤ 64) :
    Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, slot] at h₁ h₂
  have e : ∀ k, k < 6 → (a - (scr + BitVec.ofNat 64 (8 * H.W + 8 * k))).toNat =
      ((a - scr).toNat + 2 ^ 64 - (8 * H.W + 8 * k)) % 2 ^ 64 := fun k hk => by
    rw [show a - (scr + BitVec.ofNat 64 (8 * H.W + 8 * k)) = (a - scr) - BitVec.ofNat 64 (8 * H.W + 8 * k) by
      bv_omega, BitVec.toNat_sub, toNat_ofNat_lt (by omega)]
    omega
  rw [e i hi] at h₁
  rw [e j hj] at h₂
  have := (a - scr).isLt
  omega

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := by
  have k : ∀ i < 6, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega), h.rbx], by rw [k 1 (by omega), h.rbp], by rw [k 2 (by omega), h.r12],
    by rw [k 3 (by omega), h.r13], by rw [k 4 (by omega), h.r14], by rw [k 5 (by omega), h.r15]⟩

theorem ea_slot (s : State) (b : Reg) (scr : Addr) (hb : s.gpr b = scr) (i : Nat) :
    s.ea (at_ b (8 * H.W + 8 * i)) = slot H scr i := by
  rw [ea_at, ofInt_natCast, hb]

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 48 ≤ L)
    (hW : H.W ≤ 64) {i : Nat} (hi : i < 6) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega) (by omega)⟩

/-- Saving the registers, with `scratch` in `r8`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h8 : s.gpr .r8 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → Frame [saveR H scr] s.mem s'.mem →
      SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 6, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ i, t.ea (at_ .r8 (8 * H.W + 8 * i)) = slot H scr i :=
    fun hg i => by rw [ea_at, ofInt_natCast, hg, h8]
  simp only [Hash.save, Hash.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_store (a := slot H scr 0) (ea rfl 0) (io rfl 0 (by omega)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := slot H scr 1) (ea g₁ 1) (io wr₁ 1 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := slot H scr 2) (ea (g₂.trans g₁) 2) (io (wr₂.trans wr₁) 2 (by omega))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := slot H scr 3) (ea (g₃.trans (g₂.trans g₁)) 3) (io (wr₃.trans (wr₂.trans wr₁)) 3 (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := slot H scr 4) (ea (g₄.trans (g₃.trans (g₂.trans g₁))) 4)
    (io (wr₄.trans (wr₃.trans (wr₂.trans wr₁))) 4 (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := slot H scr 5) (ea (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁)))) 5)
    (io (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans wr₁)))) 5 (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have g : s₆.gpr = s.gpr := g₆.trans (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁))))
  refine k s₆ g (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_ ?_
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    have c : ∀ i < 6, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega) (by omega)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _ (c 5 (by omega)))
  · have d : ∀ i j, i < 6 → j < 6 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₆, m₅, m₄, m₃, m₂, m₁, g₅, g₄, g₃, g₂, g₁]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readW_writeW_ne _ _ (d 0 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 3 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 2 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 1 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 1 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 3 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 2 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 2 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 2 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 2 3 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 3 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 3 4 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 4 5 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `r15` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h15 : s.gpr .r15 = scr) (hW : H.W ≤ 64) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 6, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ea : ∀ {t : State}, t.gpr .r15 = scr → ∀ i, t.ea (at_ .r15 (8 * H.W + 8 * i)) = slot H scr i :=
    fun h i => by rw [ea_at, ofInt_natCast, h]
  simp only [Hash.restore, Hash.saved, List.map_cons, List.map_nil]
  refine wp_movm (a := slot H scr 0) (ea h15 0) (io rfl rfl 0 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := slot H scr 1) (ea (by rw [u₁.other _ (by decide), h15]) 1)
    (io u₁.rd u₁.wr 1 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := slot H scr 2) (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h15]) 2)
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := slot H scr 3) (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h15]) 3)
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := slot H scr 4) (ea (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₁.other _ (by decide), h15]) 4)
    (io (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))) (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))) 4
      (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := slot H scr 5) (ea (by rw [u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]) 5)
    (io (u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))))
      (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))) 5 (by omega)) fun s₆ u₆ => ?_
  refine WP.block_nil ⟨by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun r hr => ?_⟩
  · have hm : ∀ t : State, t.mem = s.mem → ∀ i, t.mem.readW (slot H scr i) 64 = s.mem.readW (slot H scr i) 64 :=
      fun t h i => by rw [h]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, hs.rbx]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, hs.rbp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        hs.r12]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hs.r13]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r14]
    · rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r15]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]

end VG.Proof.Hmac.Generic.X86_64
