import VerifiedGarbage.Proof.Hmac.Generic.X86.Loops

/-!
# HMAC over any streaming hash function on x86 (32-bit): our caller's registers

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/Save.lean`): the callee-saved registers we use
(`ebx`, `esi`, `edi`, `ebp`) are stored in `scratch` after the working
space of the functions we call (`Hash.saved`), with `scratch` in `eax`, and
loaded back at the end, with `scratch` copied from `ebp` into `eax` first.
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store sub_offset)
open VG.Proof.Hmac.Generic.Common (InRegions.right' add_ofNat_add)

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.ebx, .esi, .edi, .ebp]

theorem callee_saved : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨scr.setWidth 64 + BitVec.ofNat 64 (8 * H.W), 16⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (scr.setWidth 64 + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 16 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 16) :
    Region.Sub ⟨scr.setWidth 64 + BitVec.ofNat 64 d, 4⟩ (saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega, ← add_ofNat_add]
  exact sub_offset (by omega) (by omega)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (slot_sub H scr h₁ h₂)) (by decide)

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : SavedRegs H scr s₁ m)
    (he : ∀ r ∈ savedRegs, s₁.gpr r = s₀.gpr r) : SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

/-- The memory after storing `g r` at `B + d` for each `(r, d)` of `l`. -/
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
    refine wp_store (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2)
      (by rw [ea_at, addr_eq h1]) h2 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (fun x hx hy => by bv_omega) (by decide)

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

theorem save_eq : H.save = H.saved.map (fun p => Instr.store (at_ .eax p.2) p.1) := rfl

/-- Saving the registers, with `scratch` in `eax`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (hax : s.gpr .eax = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [hax]
    exact ⟨by omega, ⟨_, hsc, contains_offset (by omega) (by omega)⟩⟩
  · rw [m, hax]
    exact saveMem_frameR _ _ _ _ (by omega) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega) p hp

theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .eax ∧ (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_movm (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) (by rw [ea_at, addr_eq h2]) h3
      fun s₁ u₁ => ?_
    have eb : s₁.gpr .eax = s.gpr .eax := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq :
    H.restore = .mov .eax (.reg .ebp) :: H.saved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) := rfl

theorem saved_fst : H.saved.map Prod.fst = savedRegs := rfl

/-- Loading them back, with `scratch` in `ebp`. -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (hbp : s.gpr .ebp = scr) {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → r ≠ .eax → s'.gpr r = s.gpr r) := by
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr := by rw [u₁.gpr, hbp]
  rw [← List.append_nil (List.map _ _)]
  refine restoreList_ok H.saved s₁ _ (by rw [saved_fst]; decide) (fun p hp => ?_)
    fun s₂ hl ho hm hrd hwr => WP.block_nil ⟨by rw [hm, u₁.mem], by rw [hrd, u₁.rd], by rw [hwr, u₁.wr],
      fun r hr => ?_, fun r hr hr' => ?_⟩
  · have := saved_mem H hp
    refine ⟨?_, by rw [e₁]; omega, ?_⟩
    · simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    · rw [e₁, u₁.rd, u₁.wr]; exact InRegions.right' ⟨_, hsc, contains_offset (by omega) (by omega)⟩
  · have hv : ∀ p ∈ H.saved, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      rw [hl p hp, e₁, u₁.mem, hs p hp]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hv (.ebx, 8 * H.W) (by simp [Hash.saved])
    · exact hv (.esi, 8 * H.W + 4) (by simp [Hash.saved])
    · exact hv (.edi, 8 * H.W + 8) (by simp [Hash.saved])
    · exact hv (.ebp, 8 * H.W + 12) (by simp [Hash.saved])
  · rw [ho r (by rw [saved_fst]; exact hr), u₁.other r hr']

/-! ## Odds and ends -/

theorem toNat_setWidth (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- `x + o`, as a register holds it, where nothing wraps around. -/
theorem setWidth_add {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := x) (k := o) h
  simpa only [addr] using this

theorem toNat_add_ofNat {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

/-! ## The stack

The 48 bytes below `esp` lie below the return address and the arguments;
what does not write those leaves them, and our arguments, as on entry. -/

theorem stk_ret {E : BitVec 32} (hE : 48 ≤ E.toNat) (hf : E.toNat + 4 ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨E.setWidth 64, 4⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth hE] at h₁
  have := toNat_setWidth E
  generalize E.setWidth 64 = B at *
  bv_omega

theorem stk_args {E : BitVec 32} {n : Nat} (hE : 48 ≤ E.toNat) (hf : E.toNat + 4 + n ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨addr E 4, n⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth hE] at h₁
  rw [addr_eq (by omega)] at h₂
  have := toNat_setWidth E
  generalize E.setWidth 64 = B at *
  bv_omega

/-- Argument `i` is at `4 i` bytes into the arguments. -/
theorem argAddr_eq (s : State) (i : Nat) :
    argAddr s i = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := rfl

theorem arg_sub {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : Region.Sub ⟨argAddr s i, 4⟩ ⟨addr E 4, n⟩ := by
  intro a h
  simp only [Region.Contains, argAddr_eq, hs] at h ⊢
  rw [addr_eq (by omega)]
  rw [show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr E (4 + 4 * i) from rfl,
    addr_eq (by omega)] at h
  have := toNat_setWidth E
  generalize E.setWidth 64 = B at *
  bv_omega

theorem arg_contains {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : (⟨addr E 4, n⟩ : Region).Contains (argAddr s i) 4 := by
  simp only [Region.Contains, argAddr_eq, hs]
  rw [addr_eq (by omega), show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr E (4 + 4 * i) from rfl,
    addr_eq (by omega)]
  have := toNat_setWidth E
  generalize E.setWidth 64 = B at *
  bv_omega

/-- The arguments are kept by what writes elsewhere. -/
theorem arg_keep {E : BitVec 32} {s₀ s : State} (h₀ : s₀.gpr .esp = E) (hs : s.gpr .esp = E) {n : Nat}
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) {rs : List Region} (hm : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr E 4, n⟩ r) {i : Nat} (hi : 4 * i + 4 ≤ n) : arg s i = arg s₀ i := by
  simp only [arg]
  rw [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hs, h₀]]
  exact hm.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (arg_sub h₀ hi hf)) (by decide)

end VG.Proof.Hmac.Generic.X86
