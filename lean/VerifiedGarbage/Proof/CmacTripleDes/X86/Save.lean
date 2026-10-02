import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
import VerifiedGarbage.Proof.MdStream.X86.Common

/-!
# TDEA-CMAC on x86: saving and restoring the registers, and the arguments

Untrusted: everything here is checked by Lean. Each function saves our
caller's `ebx`, `esi`, `edi` and `ebp` to bytes `[84, 100)` of the scratch
buffer through `eax` (`save`), and restores them from there through `ebp`,
`ebp` last (`restore`). It loads its arguments from the stack (`wp_arg`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86
open VG.Proof.MdStream.X86 (Upd Mupd wp_movm wp_store)

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, [b + o]`. -/
theorem wp_xorma {d b : Reg} {o : Nat} {a : Addr} (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: is)) s Q := by
  subst ha
  exact Wp.wp_xorm rfl hin fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {o : Nat} {s₀ : State} (i : Nat) (ho : o = 4 + 4 * i) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp o)) :: is)) s Q :=
  wp_movm (by rw [ea_at', hesp, ho]; rfl) hin fun s' u => k s' (hv ▸ u)

end

/-! ## Saving -/

/-- The memory after storing the registers `l` (values `g`) at `B + offset`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = saveMem s.mem ((s.gpr .eax).setWidth 64) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2⟩ := hl p (by simp)
    refine wp_store (by rw [ea_at']; exact addr_eq h1) h2 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem saved_bound : ∀ p ∈ saved, 84 ≤ p.2 ∧ p.2 + 4 ≤ 100 := by decide

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (S.setWidth 64) s₀.gpr saved

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
    Frame [⟨S.setWidth 64 + BitVec.ofNat 64 84, 16⟩] s₀.mem (savedMem s₀ S) :=
  saveMem_frame' _ _ _ (by decide) saved fun p hp => saved_bound p hp

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

set_option simprocs false in
/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s₀ S).readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [savedMem, saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem save_eq : save = saved.map fun p => Instr.store (at_ .eax p.2) p.1 := rfl

/-! ## Restoring -/

/-- Restoring the registers through `b`, which none of them is. -/
theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) ((s.gpr b).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW ((s.gpr b).setWidth 64 + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.mov p.1 (.mem (at_ b p.2))) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_movm (by rw [ea_at']; exact addr_eq h1) h2 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

/-- The registers but `ebp`, and where they are saved. -/
def saved3 : List (Reg × Nat) := [(.ebx, 84), (.esi, 88), (.edi, 92)]

theorem restore_eq : restore = saved3.map (fun p => Instr.mov p.1 (.mem (at_ .ebp p.2))) ++
    ([.mov .ebp (.mem (at_ .ebp 96))] : List Instr) := rfl

/-- `restore` from the scratch buffer at `S`: each register gets its slot. -/
theorem restore_ok {s : State} {S : BitVec 32} (hb : s.gpr .ebp = S) (hS : S.toNat + 100 ≤ 2 ^ 32)
    (hr : ∀ d, 84 ≤ d → d + 4 ≤ 100 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 d) 4) :
    WP isa (.block restore) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 p.2) 32) ∧
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine restoreList_ok saved3 s _ (by decide) (fun p hp => ?_) fun s₁ hl ho hm hrd hwr => ?_
  · have : 84 ≤ p.2 ∧ p.2 + 4 ≤ 100 ∧ p.1 ≠ .ebp := by revert p; decide
    rw [hb]; exact ⟨this.2.2, by omega, hr _ this.1 this.2.1⟩
  have b₁ : s₁.gpr .ebp = S := by rw [ho _ (by decide), hb]
  refine wp_movm (a := S.setWidth 64 + BitVec.ofNat 64 96) (by rw [ea_at', b₁]; exact addr_eq (by omega))
    (by rw [hrd, hwr]; exact hr 96 (by decide) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨fun p hp => ?_, fun r hr => ?_, by rw [u₂.mem, hm], by rw [u₂.rd, hrd],
      by rw [u₂.wr, hwr]⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals first
      | (rw [u₂.gpr, hm])
      | (rw [u₂.other _ (by decide), hl _ (by simp [saved3]), hb])
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.other _ hr.2.2.2, ho r (by simp [saved3, hr.1, hr.2.1, hr.2.2.1])]

/-- The registers restored from slots that have not changed since they were
saved, with the stack pointer and the return address kept. -/
theorem restored {s₀ s s' : State} {S : BitVec 32}
    (hm : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = (savedMem s₀ S).readW (S.setWidth 64 + BitVec.ofNat 64 d) 32)
    (h : ∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (S.setWidth 64 + BitVec.ofNat 64 p.2) 32)
    (hsp : s'.gpr .esp = s₀.gpr .esp)
    (hret : s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, hret⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h (.ebx, 84) (by simp [saved]), hm 84 (by decide) (by decide),
      savedMem_slot s₀ S (r := .ebx) (d := 84) (by simp [saved])]
  · rw [h (.esi, 88) (by simp [saved]), hm 88 (by decide) (by decide),
      savedMem_slot s₀ S (r := .esi) (d := 88) (by simp [saved])]
  · rw [h (.edi, 92) (by simp [saved]), hm 92 (by decide) (by decide),
      savedMem_slot s₀ S (r := .edi) (d := 92) (by simp [saved])]
  · rw [h (.ebp, 96) (by simp [saved]), hm 96 (by decide) (by decide),
      savedMem_slot s₀ S (r := .ebp) (d := 96) (by simp [saved])]
  · exact hsp

end VG.Proof.CmacTripleDes.X86
