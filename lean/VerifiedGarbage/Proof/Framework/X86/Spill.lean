import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Target

/-!
# x86 (32-bit): saving and restoring registers in memory

A function that needs more registers than the caller lets it clobber stores
some of them in memory on entry and loads them back before it returns. Both
are a list of `(register, offset)` slots and a base register: `saveCode b l`
stores each register at `[b + offset]`, `restoreCode b l` loads it back.

* `save_ok`: after `saveCode b l` the memory is `saveMem m (addr B) g l`,
  the registers, regions and flags are unchanged.
* `restore_ok`: from memory where the slots hold `g` (`Saved`), after
  `restoreCode b l` each register of `l` is `g` of it, the others are
  unchanged (`Restored`). `restoreBase_ok` restores the base register last,
  and `Restored.abi` turns a restore of the entry registers into the ABI's
  callee-saved postcondition.
* `save_ofNat_ok`, `restore_ofNat_ok`: the same for slots inside an
  `n`-byte buffer (`Fits n l`), addressed as `(A + BitVec.ofNat 64 ·)`.
* `saveMem_saved`, `saveMem_frame`, `saveMem_readW_of_sep`: what `saveMem`
  writes, and that it writes nothing else; `Saved.of_frame`: the slots stay
  saved while the function writes elsewhere (`Saved.writeW_addr`: one store
  outside the slots).

`saveMem` and `Saved` take the address of each slot as a function of its
offset: `addr B` as the code computes it, or `(A + BitVec.ofNat 64 ·)` for a
proof that states addresses that way (`saveMem_congr`, `Saved.congr` move
between them). Each lemma is proven once, by induction over the slots; for a
literal list the side conditions (`∀ p ∈ l, …`, `Fits`) close by `decide` or
reduce to one per slot.
-/

namespace VG.X86.Spill

open VG VG.X86 VG.X86.Wp

/-- Registers and the offsets they are saved at. -/
abbrev Slots := List (Reg × Nat)

/-- `mov [b + d], r` for each slot `(r, d)`. -/
def saveCode (b : Reg) (l : Slots) : List Instr := l.map fun p => .store ⟨b, p.2⟩ p.1

/-- `mov r, [b + d]` for each slot `(r, d)`. -/
def restoreCode (b : Reg) (l : Slots) : List Instr := l.map fun p => .mov p.1 (.mem ⟨b, p.2⟩)

/-- The memory after storing `g r` at `f d` for each slot `(r, d)`, in order. -/
def saveMem (m : Mem) (f : Nat → Addr) (g : Reg → BitVec 32) : Slots → Mem
  | [] => m
  | p :: l => saveMem (m.writeW (f p.2) (g p.1)) f g l

/-- Each slot `(r, d)` at `f d` holds `g r`. -/
def Saved (m : Mem) (f : Nat → Addr) (g : Reg → BitVec 32) (l : Slots) : Prop :=
  ∀ p ∈ l, m.readW (f p.2) 32 = g p.1

/-! ## Saving -/

theorem save_ok {b : Reg} {rest : List Instr} (l : Slots) :
    ∀ {s : State} {Q : State → Prop}, (∀ p ∈ l, InRegions s.wr (addr (s.gpr b) p.2) 4) →
    (∀ s', Mupd s s' (saveMem s.mem (addr (s.gpr b)) s.gpr l) → WP isa (.block rest) s' Q) →
    WP isa (.block (saveCode b l ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    intro s Q hout k
    refine wp_stm rfl (hout p List.mem_cons_self) fun s₁ u₁ => ?_
    refine ih (fun q hq => ?_) fun s' u => k s' ⟨u.gpr.trans u₁.gpr, ?_, u.rd.trans u₁.rd,
      u.wr.trans u₁.wr, u.zf.trans u₁.zf, u.cf.trans u₁.cf⟩
    · rw [u₁.gpr, u₁.wr]; exact hout q (List.mem_cons_of_mem _ hq)
    · rw [u.mem, u₁.mem, u₁.gpr]; rfl

/-! ## Restoring -/

/-- `s'` is `s` with each register of `l` set to `g` of it. -/
structure Restored (s s' : State) (g : Reg → BitVec 32) (l : Slots) : Prop where
  gpr : ∀ p ∈ l, s'.gpr p.1 = g p.1
  other : ∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  zf : s'.zf = s.zf
  cf : s'.cf = s.cf

/-- Each register of `l`, after `restoreCode`, is `g` of it. -/
theorem Restored.regs {s s' : State} {g : Reg → BitVec 32} {l : Slots} (h : Restored s s' g l) :
    ∀ r ∈ l.map Prod.fst, s'.gpr r = g r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

theorem restore_ok {b : Reg} {rest : List Instr} {g : Reg → BitVec 32} (l : Slots) :
    ∀ {s : State} {Q : State → Prop}, (∀ p ∈ l, p.1 ≠ b) →
    (∀ p ∈ l, InRegions (s.rd ++ s.wr) (addr (s.gpr b) p.2) 4) → Saved s.mem (addr (s.gpr b)) g l →
    (∀ s', Restored s s' g l → WP isa (.block rest) s' Q) →
    WP isa (.block (restoreCode b l ++ rest)) s Q := by
  induction l with
  | nil =>
    intro s Q _ _ _ k
    exact k s ⟨fun _ h => (nomatch h), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    intro s Q hb hin hs k
    refine cons (s' := s.setReg p.1 (s.mem.readW (addr (s.gpr b) p.2) 32))
      (by simp [exec, readSrc_mem rfl (hin p List.mem_cons_self)]) ?_
    have eb : (s.setReg p.1 (s.mem.readW (addr (s.gpr b) p.2) 32)).gpr b = s.gpr b :=
      RegUpd.gpr_setReg_of_ne _ _ (hb p List.mem_cons_self).symm
    refine ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [eb]; exact hin q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [eb]; exact hs q (List.mem_cons_of_mem _ hq)) fun s' u => k s' ⟨?_, ?_,
        u.mem, u.rd, u.wr, u.zf, u.cf⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · by_cases hm : q.1 ∈ l.map Prod.fst
        · obtain ⟨q', hq', e⟩ := List.mem_map.mp hm
          rw [← e]; exact u.gpr q' hq'
        · rw [u.other _ hm, RegUpd.gpr_setReg_self]; exact hs q List.mem_cons_self
      · exact u.gpr q hq
    · intro r hr
      simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [u.other r hr.2]; exact RegUpd.gpr_setReg_of_ne _ _ hr.1

/-- `restoreCode` whose last load is of the base register. -/
theorem restoreBase_ok {b : Reg} {d : Nat} {rest : List Instr} {g : Reg → BitVec 32} (l : Slots)
    {s : State} {Q : State → Prop} (hb : ∀ p ∈ l, p.1 ≠ b)
    (hin : ∀ p ∈ l ++ [(b, d)], InRegions (s.rd ++ s.wr) (addr (s.gpr b) p.2) 4)
    (hs : Saved s.mem (addr (s.gpr b)) g (l ++ [(b, d)]))
    (k : ∀ s', Restored s s' g (l ++ [(b, d)]) → WP isa (.block rest) s' Q) :
    WP isa (.block (restoreCode b (l ++ [(b, d)]) ++ rest)) s Q := by
  have hl : ∀ p ∈ l, p ∈ l ++ [(b, d)] := fun p hp => List.mem_append_left _ hp
  have hd : (b, d) ∈ l ++ [(b, d)] := List.mem_append_right _ List.mem_cons_self
  rw [restoreCode, List.map_append, List.append_assoc]
  refine restore_ok l hb (fun p hp => hin p (hl p hp)) (fun p hp => hs p (hl p hp)) fun s₁ u₁ => ?_
  have eb : s₁.gpr b = s.gpr b := u₁.other b fun h => by
    obtain ⟨p, hp, e⟩ := List.mem_map.mp h; exact hb p hp e
  have hin' : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr b) d) 4 := by
    rw [eb, u₁.rd, u₁.wr]; exact hin (b, d) hd
  show WP isa (.block (.mov b (.mem ⟨b, d⟩) :: rest)) s₁ Q
  refine cons (s' := s₁.setReg b (s₁.mem.readW (addr (s₁.gpr b) d) 32))
    (by simp [exec, readSrc_mem rfl hin']) (k _ ⟨?_, ?_, u₁.mem, u₁.rd, u₁.wr, u₁.zf, u₁.cf⟩)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [RegUpd.gpr_setReg_of_ne _ _ (hb p hp)]; exact u₁.gpr p hp
    · rw [List.mem_singleton.mp hp, RegUpd.gpr_setReg_self, eb, u₁.mem]; exact hs (b, d) hd
  · intro r hr
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
      not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2]; exact u₁.other r hr.1

/-- The callee-saved registers after restoring all but `esp`, which the code keeps. -/
theorem Restored.abi {s s' s₀ : State} {l : Slots} (h : Restored s s' s₀.gpr l)
    (hcov : ∀ r ∈ calleeSaved, r ∈ l.map Prod.fst ∨ r = .esp) (hl : .esp ∉ l.map Prod.fst)
    (hesp : s.gpr .esp = s₀.gpr .esp) : ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  intro r hr
  rcases hcov r hr with hr | rfl
  · exact h.regs r hr
  · rw [h.other _ hl, hesp]

/-! ## The memory -/

/-- Slots inside `[B, B + n)`, which does not wrap. -/
theorem addr_eq_of {B : BitVec 32} {n d : Nat} (hB : B.toNat + n ≤ 2 ^ 32) (hd : d + 4 ≤ n) :
    addr B d = B.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by omega)

/-- Reading outside the slots. -/
theorem saveMem_readW_of_sep (f : Nat → Addr) (g : Reg → BitVec 32) {a : Addr} {w : Nat}
    (hw : w / 8 < 2 ^ 64) :
    ∀ (l : Slots) (m : Mem), (∀ p ∈ l, Mem.Sep a (w / 8) (f p.2) 4) →
      (saveMem m f g l).readW a w = m.readW a w := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons p l ih =>
    intro m h
    exact (ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)).trans
      (Mem.readW_writeW_sep (h p List.mem_cons_self) hw)

/-- `saveMem` depends on `f` and `g` only at the slots of `l`. -/
theorem saveMem_congr {f f' : Nat → Addr} {g g' : Reg → BitVec 32} :
    ∀ (l : Slots) (m : Mem), (∀ p ∈ l, f p.2 = f' p.2) → (∀ p ∈ l, g p.1 = g' p.1) →
      saveMem m f g l = saveMem m f' g' l := by
  intro l
  induction l with
  | nil => intro m _ _; rfl
  | cons p l ih =>
    intro m hf hg
    simp only [saveMem]
    rw [hf p List.mem_cons_self, hg p List.mem_cons_self]
    exact ih _ (fun q hq => hf q (List.mem_cons_of_mem _ hq)) fun q hq => hg q (List.mem_cons_of_mem _ hq)

/-- Each slot is written last. -/
theorem saveMem_saved (m : Mem) {f : Nat → Addr} (g : Reg → BitVec 32) :
    ∀ (l : Slots), l.Pairwise (fun p q => Mem.Sep (f p.2) 4 (f q.2) 4) →
      Saved (saveMem m f g l) f g l := by
  intro l
  induction l generalizing m with
  | nil => intro _ _ h; nomatch h
  | cons p l ih =>
    intro hp q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (saveMem_readW_of_sep f g (by decide) l _ fun r hr => List.rel_of_pairwise_cons hp hr).trans
        (Mem.readW_writeW_self32 _ _ _)
    · exact ih _ hp.of_cons q hq

/-- `saveMem` writes only the slots, in `R`. -/
theorem saveMem_frame {rs : List Region} {R : Region} (hR : R ∈ rs) (f : Nat → Addr)
    (g : Reg → BitVec 32) :
    ∀ (l : Slots) (m : Mem), (∀ p ∈ l, R.Contains (f p.2) 4) → Frame rs m (saveMem m f g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m h
    exact ((Frame.refl _ _).writeW hR _ (h p List.mem_cons_self)).trans
      (ih _ fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## Slots in a buffer -/

/-- The slots of `l` are in `[0, n)` and do not overlap. -/
def Fits (n : Nat) (l : Slots) : Prop :=
  (∀ p ∈ l, p.2 + 4 ≤ n) ∧ l.Pairwise fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2

instance (n : Nat) (l : Slots) : Decidable (Fits n l) := by unfold Fits; infer_instance

/-- Fitting slots at `A + d` are separate. -/
theorem Fits.sep_ofNat {n : Nat} {l : Slots} (hl : Fits n l) (A : Addr) (hn : n ≤ 2 ^ 64) :
    l.Pairwise fun p q => Mem.Sep (A + BitVec.ofNat 64 p.2) 4 (A + BitVec.ofNat 64 q.2) 4 :=
  List.Pairwise.imp_of_mem (fun hp hq h => Offset.sep _ h (by have := hl.1 _ hp; omega)
    (by have := hl.1 _ hq; omega)) hl.2

/-- Fitting slots at `addr B d`, in `[B, B + n)`, are separate. -/
theorem Fits.sep_addr {n : Nat} {l : Slots} (hl : Fits n l) {B : BitVec 32} (hB : B.toNat + n ≤ 2 ^ 32) :
    l.Pairwise fun p q => Mem.Sep (addr B p.2) 4 (addr B q.2) 4 :=
  List.Pairwise.imp_of_mem (fun hp hq h => by
    rw [addr_eq_of hB (hl.1 _ hp), addr_eq_of hB (hl.1 _ hq)]; exact h) (hl.sep_ofNat _ (by omega))

/-- `saveMem_saved` for fitting slots at `A + d`. -/
theorem saveMem_saved_ofNat (m : Mem) (A : Addr) (g : Reg → BitVec 32) {n : Nat} {l : Slots} (hl : Fits n l)
    (hn : n ≤ 2 ^ 64) : Saved (saveMem m (A + BitVec.ofNat 64 ·) g l) (A + BitVec.ofNat 64 ·) g l :=
  saveMem_saved m g l (hl.sep_ofNat A hn)

/-- `saveMem_saved` for fitting slots at `addr B d`, in `[B, B + n)`. -/
theorem saveMem_saved_addr (m : Mem) {B : BitVec 32} (g : Reg → BitVec 32) {n : Nat} {l : Slots} (hl : Fits n l)
    (hB : B.toNat + n ≤ 2 ^ 32) : Saved (saveMem m (addr B) g l) (addr B) g l :=
  saveMem_saved m g l (hl.sep_addr hB)

/-- The slots of `l` at `addr B d` are in `[B, B + n)`. -/
theorem contains_of_fits {B : BitVec 32} {n : Nat} (hB : B.toNat + n ≤ 2 ^ 32) {l : Slots}
    (hl : Fits n l) : ∀ p ∈ l, Region.Contains ⟨B.setWidth 64, n⟩ (addr B p.2) 4 := by
  intro p hp
  have h := hl.1 p hp
  rw [addr_eq_of hB h]
  exact Offset.contains_base _ h (by omega)

/-- `addr B d`, for the slots of `l` in `[B, B + n)`, is `B + d` in 64 bits. -/
theorem addr_eq_of_fits {B : BitVec 32} {n : Nat} (hB : B.toNat + n ≤ 2 ^ 32) {l : Slots}
    (hl : Fits n l) : ∀ p ∈ l, addr B p.2 = B.setWidth 64 + BitVec.ofNat 64 p.2 :=
  fun p hp => addr_eq_of hB (hl.1 p hp)

/-! ## Slots at `B + d` in 64 bits -/

/-- `save_ok`, with the slots at `B + d` in 64 bits. -/
theorem save_ofNat_ok {b : Reg} {rest : List Instr} (l : Slots) {n : Nat} (hl : Fits n l)
    {s : State} {Q : State → Prop} (hB : (s.gpr b).toNat + n ≤ 2 ^ 32)
    (hout : ∀ p ∈ l, InRegions s.wr ((s.gpr b).setWidth 64 + BitVec.ofNat 64 p.2) 4)
    (k : ∀ s', Mupd s s' (saveMem s.mem ((s.gpr b).setWidth 64 + BitVec.ofNat 64 ·) s.gpr l) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (saveCode b l ++ rest)) s Q :=
  save_ok l (fun p hp => by rw [addr_eq_of_fits hB hl p hp]; exact hout p hp) fun s' u => k s' (by
    rwa [saveMem_congr (f' := ((s.gpr b).setWidth 64 + BitVec.ofNat 64 ·)) l s.mem (addr_eq_of_fits hB hl)
      fun _ _ => rfl] at u)

/-- `restore_ok`, with the slots at `B + d` in 64 bits. -/
theorem restore_ofNat_ok {b : Reg} {rest : List Instr} {g : Reg → BitVec 32} (l : Slots) {n : Nat}
    (hl : Fits n l) {s : State} {Q : State → Prop} (hB : (s.gpr b).toNat + n ≤ 2 ^ 32)
    (hb : ∀ p ∈ l, p.1 ≠ b)
    (hin : ∀ p ∈ l, InRegions (s.rd ++ s.wr) ((s.gpr b).setWidth 64 + BitVec.ofNat 64 p.2) 4)
    (hs : Saved s.mem ((s.gpr b).setWidth 64 + BitVec.ofNat 64 ·) g l)
    (k : ∀ s', Restored s s' g l → WP isa (.block rest) s' Q) :
    WP isa (.block (restoreCode b l ++ rest)) s Q :=
  restore_ok l hb (fun p hp => by rw [addr_eq_of_fits hB hl p hp]; exact hin p hp)
    (fun p hp => by rw [addr_eq_of_fits hB hl p hp]; exact hs p hp) k

/-! ## Keeping the slots saved -/

theorem Saved.of_readW {m m' : Mem} {f : Nat → Addr} {g : Reg → BitVec 32} {l : Slots}
    (hs : Saved m f g l) (h : ∀ p ∈ l, m'.readW (f p.2) 32 = m.readW (f p.2) 32) :
    Saved m' f g l :=
  fun p hp => (h p hp).trans (hs p hp)

/-- The slots, in `[B, B + n)`, stay saved across a write at `addr B e` beside them. -/
theorem Saved.writeW_addr {m : Mem} {B : BitVec 32} {g : Reg → BitVec 32} {l : Slots} {n e w : Nat}
    (hs : Saved m (addr B) g l) (hB : B.toNat + n ≤ 2 ^ 32) (hl : ∀ p ∈ l, p.2 + 4 ≤ n) (he : e + w / 8 ≤ n)
    (hsep : ∀ p ∈ l, p.2 + 4 ≤ e ∨ e + w / 8 ≤ p.2) (v : BitVec w) (hw : 0 < w / 8 := by decide) :
    Saved (m.writeW (addr B e) v) (addr B) g l :=
  hs.of_readW fun p hp => by
    have h := hl p hp
    rw [addr_eq_of hB h, addr_eq (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (hsep p hp) (by omega) (by omega)) (by decide)

/-- The slots, in `R`, stay saved across writes to regions disjoint from `R`. -/
theorem Saved.of_frame {m m' : Mem} {f : Nat → Addr} {g : Reg → BitVec 32} {l : Slots}
    {rs : List Region} {R : Region} (hs : Saved m f g l) (hf : Frame rs m m')
    (hR : ∀ p ∈ l, R.Contains (f p.2) 4) (hd : ∀ r ∈ rs, R.Disjoint r) : Saved m' f g l :=
  hs.of_readW fun p hp => hf.readW (hR p hp) hd (by decide)

/-- The slots of `l'`, all of them slots of `l` (e.g. restored in another order). -/
theorem Saved.sub {m : Mem} {f : Nat → Addr} {g : Reg → BitVec 32} {l l' : Slots}
    (hs : Saved m f g l) (h : ∀ p ∈ l', p ∈ l) : Saved m f g l' :=
  fun p hp => hs p (h p hp)

theorem Saved.congr {m : Mem} {f f' : Nat → Addr} {g g' : Reg → BitVec 32} {l : Slots}
    (hs : Saved m f g l) (hf : ∀ p ∈ l, f p.2 = f' p.2) (hg : ∀ p ∈ l, g p.1 = g' p.1) :
    Saved m f' g' l :=
  fun p hp => (hf p hp) ▸ (hs p hp).trans (hg p hp)

end VG.X86.Spill
