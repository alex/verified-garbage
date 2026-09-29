import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Loops
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Save

/-!
# HMAC over any streaming hash function on AArch64: our caller's registers

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Save.lean`): the six callee-saved registers we
use, and our return address `x30`, are stored in `scratch` after the working
space of the functions we call (`Hash.saved`), and loaded back at the end,
`x23` (which holds `scratch`) last.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Sha256.X86_64 (contains_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_str wp_ldr)
open VG.Proof.Hmac.Generic.X86_64 (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x30, .x23]

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 56⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  x19 : m.readW (slot H scr 0) 64 = s₀.gpr .x19
  x20 : m.readW (slot H scr 1) 64 = s₀.gpr .x20
  x21 : m.readW (slot H scr 2) 64 = s₀.gpr .x21
  x22 : m.readW (slot H scr 3) 64 = s₀.gpr .x22
  x24 : m.readW (slot H scr 4) 64 = s₀.gpr .x24
  x30 : m.readW (slot H scr 5) 64 = s₀.gpr .x30
  x23 : m.readW (slot H scr 6) 64 = s₀.gpr .x23

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 7) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.Sha256.X86_64.sub_offset (by omega) (by omega)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 7) (hj : j < 7) (hij : i ≠ j) (hW : H.W ≤ 64) :
    Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, slot] at h₁ h₂
  have e : ∀ k, k < 7 → (a - (scr + BitVec.ofNat 64 (8 * H.W + 8 * k))).toNat =
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
  have k : ∀ i < 7, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega), h.x19], by rw [k 1 (by omega), h.x20], by rw [k 2 (by omega), h.x21],
    by rw [k 3 (by omega), h.x22], by rw [k 4 (by omega), h.x24], by rw [k 5 (by omega), h.x30],
    by rw [k 6 (by omega), h.x23]⟩

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 56 ≤ L)
    (hW : H.W ≤ 64) {i : Nat} (hi : i < 7) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega) (by omega)⟩

theorem slot_eq (scr : Addr) {o : Nat} (i : Nat) (h : o = 8 * H.W + 8 * i) :
    scr + BitVec.ofNat 64 o = slot H scr i := by rw [h]

/-- Saving the registers, with `scratch` in `x4`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h4 : s.gpr .x4 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 7, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x4 + BitVec.ofNat 64 o = slot H scr i := fun hg o i h => by rw [hg, h4, h]
  simp only [Hash.save, Hash.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_str (a := slot H scr 0) (by have := ho 0 (by omega); omega) (ea rfl 0 (by omega))
    (io rfl 0 (by omega)) fun s₁ m₁ => ?_
  refine wp_str (a := slot H scr 1) (by have := ho 1 (by omega); omega) (ea m₁.gpr 1 (by omega))
    (io m₁.wr 1 (by omega)) fun s₂ m₂ => ?_
  have g₂ : s₂.gpr = s.gpr := m₂.gpr.trans m₁.gpr
  have w₂ : s₂.wr = s.wr := m₂.wr.trans m₁.wr
  refine wp_str (a := slot H scr 2) (by have := ho 2 (by omega); omega) (ea g₂ 2 (by omega))
    (io w₂ 2 (by omega)) fun s₃ m₃ => ?_
  have g₃ : s₃.gpr = s.gpr := m₃.gpr.trans g₂
  have w₃ : s₃.wr = s.wr := m₃.wr.trans w₂
  refine wp_str (a := slot H scr 3) (by have := ho 3 (by omega); omega) (ea g₃ 3 (by omega))
    (io w₃ 3 (by omega)) fun s₄ m₄ => ?_
  have g₄ : s₄.gpr = s.gpr := m₄.gpr.trans g₃
  have w₄ : s₄.wr = s.wr := m₄.wr.trans w₃
  refine wp_str (a := slot H scr 4) (by have := ho 4 (by omega); omega) (ea g₄ 4 (by omega))
    (io w₄ 4 (by omega)) fun s₅ m₅ => ?_
  have g₅ : s₅.gpr = s.gpr := m₅.gpr.trans g₄
  have w₅ : s₅.wr = s.wr := m₅.wr.trans w₄
  refine wp_str (a := slot H scr 5) (by have := ho 5 (by omega); omega) (ea g₅ 5 (by omega))
    (io w₅ 5 (by omega)) fun s₆ m₆ => ?_
  have g₆ : s₆.gpr = s.gpr := m₆.gpr.trans g₅
  have w₆ : s₆.wr = s.wr := m₆.wr.trans w₅
  refine wp_str (a := slot H scr 6) (by have := ho 6 (by omega); omega) (ea g₆ 6 (by omega))
    (io w₆ 6 (by omega)) fun s₇ m₇ => ?_
  refine k s₇ (m₇.gpr.trans g₆) (by rw [m₇.rd, m₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd])
    (m₇.wr.trans w₆) (by rw [m₇.sp, m₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp]) ?_ ?_
  · rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    have c : ∀ i < 7, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega) (by omega)
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega))).writeW (List.mem_singleton_self _) _ (c 6 (by omega)))
  · have d : ∀ i j, i < 7 → j < 7 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, g₆, g₅, g₄, g₃, g₂, m₁.gpr]
    have w : ∀ i j, i < 7 → j < 7 → i ≠ j → ∀ (m : Mem) (v : BitVec 64),
        (m.writeW (slot H scr j) v).readW (slot H scr i) 64 = m.readW (slot H scr i) 64 :=
      fun i j hi hj hij m v => readW_writeW_ne _ _ (d i j hi hj hij)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w 0 6 (by omega) (by omega) (by omega), w 0 5 (by omega) (by omega) (by omega),
        w 0 4 (by omega) (by omega) (by omega), w 0 3 (by omega) (by omega) (by omega),
        w 0 2 (by omega) (by omega) (by omega), w 0 1 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self64]
    · rw [w 1 6 (by omega) (by omega) (by omega), w 1 5 (by omega) (by omega) (by omega),
        w 1 4 (by omega) (by omega) (by omega), w 1 3 (by omega) (by omega) (by omega),
        w 1 2 (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [w 2 6 (by omega) (by omega) (by omega), w 2 5 (by omega) (by omega) (by omega),
        w 2 4 (by omega) (by omega) (by omega), w 2 3 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self64]
    · rw [w 3 6 (by omega) (by omega) (by omega), w 3 5 (by omega) (by omega) (by omega),
        w 3 4 (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [w 4 6 (by omega) (by omega) (by omega), w 4 5 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self64]
    · rw [w 5 6 (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `x23` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h23 : s.gpr .x23 = scr) (hW : H.W ≤ 64) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 7, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega
  have ea : ∀ {t : State}, t.gpr .x23 = scr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x23 + BitVec.ofNat 64 o = slot H scr i := fun h o i ho => by rw [h, ho]
  simp only [Hash.restore, Hash.saved, List.map_cons, List.map_nil]
  refine wp_ldr (a := slot H scr 0) (by have := ho 0 (by omega); omega) (ea h23 0 (by omega))
    (io rfl rfl 0 (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := slot H scr 1) (by have := ho 1 (by omega); omega)
    (ea (by rw [u₁.other _ (by decide), h23]) 1 (by omega)) (io u₁.rd u₁.wr 1 (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (a := slot H scr 2) (by have := ho 2 (by omega); omega)
    (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h23]) 2 (by omega))
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (a := slot H scr 3) (by have := ho 3 (by omega); omega)
    (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]) 3 (by omega))
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega)) fun s₄ u₄ => ?_
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have x₄ : s₄.gpr .x23 = scr := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]
  refine wp_ldr (a := slot H scr 4) (by have := ho 4 (by omega); omega) (ea x₄ 4 (by omega))
    (io r₄ w₄ 4 (by omega)) fun s₅ u₅ => ?_
  refine wp_ldr (a := slot H scr 5) (by have := ho 5 (by omega); omega)
    (ea (by rw [u₅.other _ (by decide), x₄]) 5 (by omega)) (io (u₅.rd.trans r₄) (u₅.wr.trans w₄) 5 (by omega))
    fun s₆ u₆ => ?_
  refine wp_ldr (a := slot H scr 6) (by have := ho 6 (by omega); omega)
    (ea (by rw [u₆.other _ (by decide), u₅.other _ (by decide), x₄]) 6 (by omega))
    (io (u₆.rd.trans (u₅.rd.trans r₄)) (u₆.wr.trans (u₅.wr.trans w₄)) 6 (by omega)) fun s₇ u₇ => ?_
  refine WP.block_nil ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, r₄], by rw [u₇.wr, u₆.wr, u₅.wr, w₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, fun r hr => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.x19]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.x20]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.x22]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x24]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x30]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x23]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2,
      u₁.other r h1]

end VG.Proof.Hmac.Generic.AArch64
