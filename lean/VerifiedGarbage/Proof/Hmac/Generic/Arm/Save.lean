import VerifiedGarbage.Proof.Hmac.Generic.Arm.Loops

/-!
# HMAC over any streaming hash function on 32-bit ARM: our caller's registers

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Save.lean`): the callee-saved registers we use,
and our return address `lr`, are stored in `scratch` after the working space
of the functions we call (`Hash.saved`), with `scratch` in `r12`, and loaded
back at the end, with `scratch` in `r11`, which is loaded last.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream (Upd wp_ldr saveMem saveList_ok readW_writeW_save sub_offset)
open VG.Proof.Hmac.Generic.X86_64 (InRegions.right' add_ofNat_add)

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr, .r11]

theorem preserved_saved : ∀ r ∈ preserved, r ∈ savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨State.addr scr + BitVec.ofNat 64 (8 * H.W), 36⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 36 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 36) :
    Region.Sub ⟨State.addr scr + BitVec.ofNat 64 d, 4⟩ (saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega, ← add_ofNat_add]
  exact sub_offset (by omega) (by omega)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (slot_sub H scr h₁ h₂)) (by decide)

theorem saveMem_other (m : Mem) (B : Addr) (g : Reg → BitVec 32) {d : Nat} (hd : d < 2 ^ 32) :
    ∀ l : List (Reg × Nat), (∀ q ∈ l, q.2 < 2 ^ 32 ∧ (d + 4 ≤ q.2 ∨ q.2 + 4 ≤ d)) →
    (saveMem m B g l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | [], _ => rfl
  | q :: l, h => by
    rw [saveMem, saveMem_other _ B g hd l fun q' hq' => h q' (List.mem_cons_of_mem _ hq'),
      readW_writeW_save _ _ _ hd (h q (by simp)).1 (h q (by simp)).2]

theorem saveMem_read (B : Addr) (g : Reg → BitVec 32) :
    ∀ (m : Mem) (l : List (Reg × Nat)), l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    (∀ p ∈ l, p.2 < 2 ^ 32) → ∀ p ∈ l, (saveMem m B g l).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1
  | _, [], _, _, p, hp => by cases hp
  | m, q :: l, hpw, hb, p, hp => by
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [saveMem, saveMem_other _ _ _ (hb p (by simp)) l
        (fun q' hq' => ⟨hb q' (List.mem_cons_of_mem _ hq'), hpw.1 q' hq'⟩), Mem.readW_writeW_self32]
    · rw [saveMem]
      exact saveMem_read B g _ l hpw.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq')) p hp

theorem saveMem_frameR (B : Addr) (g : Reg → BitVec 32) (o L : Nat) (hL : o + L < 2 ^ 64) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, o ≤ p.2 ∧ p.2 + 4 ≤ o + L) →
    Frame [⟨B + BitVec.ofNat 64 o, L⟩] m (saveMem m B g l)
  | _, [], _ => Frame.refl _ _
  | m, p :: l, hl => by
    obtain ⟨h₁, h₂⟩ := hl p (by simp)
    have c : (⟨B + BitVec.ofNat 64 o, L⟩ : Region).Contains (B + BitVec.ofNat 64 p.2) (32 / 8) := by
      rw [show p.2 = o + (p.2 - o) by omega, ← add_ofNat_add]
      exact contains_offset (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c).trans
      (saveMem_frameR B g o L hL _ l fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem save_eq : H.save = H.saved.map (fun p => Instr.str p.1 .r12 p.2) := rfl

/-- Saving the registers, with `scratch` in `r12`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (h12 : s.gpr .r12 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [h12]
    exact ⟨by omega, by omega, ⟨_, hsc, contains_offset (by omega) (by omega)⟩⟩
  · rw [m, h12]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, h12]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

/-- The slots loaded before `r11`. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 8 * H.W), (.r5, 8 * H.W + 4), (.r6, 8 * H.W + 8), (.r7, 8 * H.W + 12), (.r8, 8 * H.W + 16),
    (.r9, 8 * H.W + 20), (.r10, 8 * H.W + 24), (.lr, 8 * H.W + 28)]

theorem restore_eq :
    H.restore = (saved8 H).map (fun p => Instr.ldr p.1 .r11 p.2) ++ ([.ldr .r11 .r11 (8 * H.W + 32)] : List Instr) := rfl

theorem saved8_fst : (saved8 H).map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr] := rfl

theorem saved8_sub {p : Reg × Nat} (hp : p ∈ saved8 H) : p ∈ H.saved := by
  simp only [saved8, Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with h | h | h | h | h | h | h | h <;> simp [h]

/-- Loading them back, with `scratch` in `r11` (loaded last). -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (h11 : s.gpr .r11 = scr) (hW : H.W ≤ 64)
    {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {d}, d + 4 ≤ L →
      InRegions (t.rd ++ t.wr) (State.addr scr + BitVec.ofNat 64 d) 4 := fun hr hw d hd => by
    rw [hr, hw]; exact InRegions.right' ⟨_, hsc, contains_offset hd (by omega)⟩
  rw [restore_eq]
  refine restoreList_ok (saved8 H) s _ (by rw [saved8_fst]; decide) (fun p hp => ?_)
    fun s₁ hl ho hm hrd hwr hsp => ?_
  · have := saved_mem H (saved8_sub H hp)
    refine ⟨?_, by omega, by rw [h11]; omega, by rw [h11]; exact io rfl rfl (by omega)⟩
    simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have e11 : s₁.gpr .r11 = scr := by
    rw [ho _ (by rw [saved8_fst]; decide), h11]
  refine wp_ldr (by omega) (addr_add (by rw [e11]; omega)) (by rw [e11]; exact io hrd hwr (by omega))
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, hm], by rw [u.rd, hrd], by rw [u.wr, hwr], by rw [u.sp, hsp],
      fun r hr => ?_, fun r hr => ?_⟩
  · have hv : ∀ p ∈ saved8 H, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      have h1 : p.1 ≠ .r11 := by
        simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
      rw [u.other _ h1, hl p hp, h11, hs p (saved8_sub H hp)]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv (.r4, 8 * H.W) (by simp [saved8])
    · exact hv (.r5, 8 * H.W + 4) (by simp [saved8])
    · exact hv (.r6, 8 * H.W + 8) (by simp [saved8])
    · exact hv (.r7, 8 * H.W + 12) (by simp [saved8])
    · exact hv (.r8, 8 * H.W + 16) (by simp [saved8])
    · exact hv (.r9, 8 * H.W + 20) (by simp [saved8])
    · exact hv (.r10, 8 * H.W + 24) (by simp [saved8])
    · exact hv (.lr, 8 * H.W + 28) (by simp [saved8])
    · rw [u.gpr, e11, hm, hs (.r11, 8 * H.W + 32) (by simp [Hash.saved])]
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other r hr.2.2.2.2.2.2.2.2, ho r (by
      rw [saved8_fst]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1⟩)]

theorem saved_ne {p : Reg × Nat} (hp : p ∈ H.saved) {r : Reg} (hr : r ∉ savedRegs) : p.1 ≠ r := by
  rintro rfl
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hr

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : SavedRegs H scr s₁ m)
    (he : ∀ r ∈ savedRegs, s₁.gpr r = s₀.gpr r) : SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Odds and ends -/

theorem below_eq {s t : State} (h : s.sp = t.sp) : below s = below t := by simp only [below, h]

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

end VG.Proof.Hmac.Generic.Arm
