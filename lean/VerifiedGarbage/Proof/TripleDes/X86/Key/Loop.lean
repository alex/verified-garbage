import VerifiedGarbage.Proof.TripleDes.X86.Key.Compare
import VerifiedGarbage.Proof.TripleDes.X86.Key.Memory

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : BitVec 32) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .esi = (keyPrefix key j).1.setWidth 32
  d : s.gpr .edi = (keyPrefix key j).2.1.setWidth 32
  counter : roundCount s = BitVec.ofNat 32 j
  pointer : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [scheduleRegion base, workRegion origin] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem keyWordAddr (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j t : Nat) (hj : j < 16) (ht : t < 2) :
    wordAddr (base + BitVec.ofNat 32 (8 * j)) t =
      addr32 base + BitVec.ofNat 64 (8 * j + 4 * t) := by
  change addr (base + BitVec.ofNat 32 (8 * j)) (4 * t) = _
  rw [addr_eq (by have h := pointer_fit base fit j hj; omega)]
  change addr32 (base + BitVec.ofNat 32 (8 * j)) + BitVec.ofNat 64 (4 * t) = _
  rw [VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega), Offset.add_ofNat_add_ofNat]

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  have hoks : Ok sboxCfg s := hok.congr hs.bp hs.bp hs.rd hs.wr
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter hoks)
  intro s₁ h₁
  have bp₁ : s₁.gpr .ebp = origin.gpr .ebp := (h₁.keep.reg .ebp (by decide)).trans hs.bp
  have sp₁ : s₁.gpr .esp = origin.gpr .esp := (h₁.keep.reg .esp (by decide)).trans hs.sp
  have ptr₁ : roundKeyPtr s₁ = roundKeyPtr s := by
    unfold roundKeyPtr
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  have count₁ : roundCount s₁ = roundCount s := by
    unfold roundCount
    rw [h₁.keep.reg .ebp (by decide), h₁.keep.mem]
  have hok₁ : Ok sboxCfg s₁ := hok.congr bp₁ bp₁ (h₁.keep.rd.trans hs.rd) (h₁.keep.wr.trans hs.wr)
  have fit₁ : (roundKeyPtr s₁).toNat + 8 ≤ 2 ^ 32 := by
    rw [ptr₁, hs.pointer]; exact pointer_fit base fit j hj
  have write₁ : ∀ t < 2, InRegions s₁.wr (wordAddr (roundKeyPtr s₁) t) 4 := by
    intro t ht
    rw [h₁.keep.wr, hs.wr, ptr₁, hs.pointer, keyWordAddr base fit j t hj ht]
    exact hw j hj t ht
  have sep₁ : ∀ t < 2, Mem.Sep (wordAddr (s₁.gpr .ebp) 5) 4 (wordAddr (roundKeyPtr s₁) t) 4 := by
    intro t ht
    rw [bp₁, ptr₁, hs.pointer, keyWordAddr base fit j t hj ht]
    exact hdis.symm.sep (work_slot origin hok.fit 5 (Or.inr rfl))
      (Offset.contains_base _ (by omega) (by omega))
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d (count₁.trans hs.counter) hok₁ fit₁ write₁ sep₁)
  intro s₂ h₂
  let k := (Spec.TripleDes.permute Spec.TripleDes.pc2
    ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
      (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64
  have addr₁ : wordAddr (roundKeyPtr s₁) 0 = addr32 base + BitVec.ofNat 64 (8 * j) := by
    rw [ptr₁, hs.pointer, keyWordAddr base fit j 0 hj (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  have hm : s₂.mem = ((s.mem.writeW (addr32 base + BitVec.ofNat 64 (8 * j)) k).writeW
      (wordAddr (origin.gpr .ebp) 4) (base + BitVec.ofNat 32 (8 * j) + 8)).writeW
      (wordAddr (origin.gpr .ebp) 5) (BitVec.ofNat 32 j + 1) := by
    rw [h₂.mem, keyStoreMem, addr₁, ptr₁, hs.pointer, count₁, hs.counter, bp₁, h₁.keep.mem]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.keep.rd.trans hs.rd),
    h₂.wr.trans (h₁.keep.wr.trans hs.wr), (h₂.reg .ebp (by decide)).trans bp₁,
    (h₂.reg .esp (by decide)).trans sp₁, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .esi (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .edi (by decide)).trans h₁.d
  · rw [h₂.ptr, ptr₁, hs.pointer]
    change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · intro i hi hi16
    have hsep (t : Nat) (ht : t = 4 ∨ t = 5) :
        Mem.Sep (addr32 base + BitVec.ofNat 64 (8 * i)) 8 (wordAddr (origin.gpr .ebp) t) 4 :=
      hdis.sep (schedule_contains base i hi16) (work_slot origin hok.fit t ht)
    rw [hm, Mem.readW_writeW_sep (hsep 5 (Or.inr rfl)) (by decide),
      Mem.readW_writeW_sep (hsep 4 (Or.inl rfl)) (by decide), keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (addr32 base) (by omega) (by omega)
        (by omega)) (by decide), hs.keys i (by omega) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · have fr := keyStore_frame s₁ base j hj fit hok₁.fit (ptr₁.trans hs.pointer) k
    rw [← h₂.mem] at fr
    have hreg : workRegion s₁ = workRegion origin := by unfold workRegion; rw [bp₁]
    rw [hreg, h₁.keep.mem] at fr
    exact hs.frame.trans fr

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg origin)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion origin))
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.X86.Key.rotation (.block Impl.TripleDes.X86.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin fit hok hw hdis (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : BitVec 32) (s : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (hok : Ok sboxCfg s)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 base + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion base).Disjoint (workRegion s))
    (hc : s.gpr .esi = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .edi = (keyInitial key).2.1.setWidth 32)
    (hcount : roundCount s = 0) (hptr : roundKeyPtr s = base) :
    WP isa (.loop (.seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.X86.Key.rotation
      (.block Impl.TripleDes.X86.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s fit hok hw hdis) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.X86.Key
