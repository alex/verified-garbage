import VerifiedGarbage.Proof.CmacTripleDes.Arm.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Block
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# TDEA-CMAC on ARMv7: saving and restoring the registers

Untrusted: everything here is checked by Lean. Each function saves our
caller's callee-saved registers to bytes `[52, 88)` of the scratch buffer
(`save`), and restores them from there through `r10`, `r10` last
(`restore`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr saveMem readW_writeW_save)

theorem saved_bound : ∀ p ∈ saved, 52 ≤ p.2 ∧ p.2 + 4 ≤ 88 := by decide

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr saved

theorem saveMem_congr (m : Mem) (B : Addr) {g g' : Reg → BitVec 32} :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, g p.1 = g' p.1) → saveMem m B g l = saveMem m B g' l := by
  intro l
  induction l generalizing m with
  | nil => intro _; rfl
  | cons p l ih =>
    intro h
    simp only [saveMem]
    rw [h p (List.mem_cons_self ..)]
    exact ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- Saving changes only bytes `[lo, lo + L)`. -/
theorem saveMem_frame' (m : Mem) (B : Addr) (g : Reg → BitVec 32) {lo L : Nat} (hL : lo + L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 4 ≤ lo + L) →
      Frame [⟨B + BitVec.ofNat 64 lo, L⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))
    rw [show B + BitVec.ofNat 64 p.2 = B + BitVec.ofNat 64 lo + BitVec.ofNat 64 (p.2 - lo) from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨State.addr S + BitVec.ofNat 64 52, 36⟩] s₀.mem (savedMem s₀ S) :=
  saveMem_frame' _ _ _ (by decide) saved fun p hp => saved_bound p hp

set_option simprocs false in
/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [savedMem, saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- Restoring the registers through `b`, which none of them is. -/
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

/-- The registers but `r10`, and where they are saved. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 52), (.r5, 56), (.r6, 60), (.r7, 64), (.r8, 68), (.r9, 72), (.r11, 76), (.lr, 80)]

theorem restore_eq : restore = saved8.map (fun p => Instr.ldr p.1 .r10 p.2) ++ ([.ldr .r10 .r10 84] : List Instr) := rfl

/-- `restore` from the scratch buffer at `S`: each register gets its slot. -/
theorem restore_ok {s : State} {S : BitVec 32} (hb : s.gpr .r10 = S) (hS : S.toNat + 88 ≤ 2 ^ 32)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 88 → InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 d) 4) :
    WP isa (.block restore) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine restoreList_ok saved8 s _ (by decide) (fun p hp => ?_) fun s₁ hl ho hm hrd hwr hsp => ?_
  · have : 52 ≤ p.2 ∧ p.2 + 4 ≤ 88 ∧ p.1 ≠ .r10 := by revert p; decide
    rw [hb]; exact ⟨this.2.2, by omega, by omega, hr _ this.1 this.2.1⟩
  have b₁ : s₁.gpr .r10 = S := by rw [ho _ (by decide), hb]
  refine wp_ldr (by decide) (addr_add (by rw [b₁]; omega)) (by rw [hrd, hwr, b₁]; exact hr 84 (by decide) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨fun p hp => ?_, by rw [u₂.sp, hsp], by rw [u₂.mem, hm], by rw [u₂.rd, hrd],
      by rw [u₂.wr, hwr]⟩
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (rw [u₂.gpr, hm, b₁])
    | (rw [u₂.other _ (by decide), hl _ (by simp [saved8]), hb])

/-- The registers restored from slots that have not changed since they were
saved. -/
theorem restored {s₀ s s' : State} {S : BitVec 32}
    (hm : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 = (savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32)
    (h : ∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, hsp⟩
  obtain ⟨d, hd⟩ : ∃ d, (r, d) ∈ saved := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨52, by simp [saved]⟩, ⟨56, by simp [saved]⟩, ⟨60, by simp [saved]⟩, ⟨64, by simp [saved]⟩,
      ⟨68, by simp [saved]⟩, ⟨72, by simp [saved]⟩, ⟨84, by simp [saved]⟩, ⟨76, by simp [saved]⟩,
      ⟨80, by simp [saved]⟩]
  have hb := saved_bound _ hd
  rw [h _ hd, hm d hb.1 hb.2, savedMem_slot s₀ S hd]

end VG.Proof.CmacTripleDes.Arm
