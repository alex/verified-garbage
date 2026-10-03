import VerifiedGarbage.Proof.TripleDes.X86.Key.Copy
import VerifiedGarbage.Proof.TripleDes.X86.Pre
import VerifiedGarbage.Proof.TripleDes.KeyMemory

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (componentKeys componentOffset)

def keyLength (s : State) : Nat := (arg s 1).toNat
abbrev keyR (s : State) : Region := ⟨addr32 (keyArg s), keyLength s⟩
abbrev outputR (s : State) : Region := ⟨addr32 (scheduleArg s), 384⟩
def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (addr32 (scheduleArg origin)) c j) 64 =
    ((componentKeys origin.mem (addr32 (keyArg origin)) (keyLength origin) c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  args : ∀ i < 4, arg s i = arg origin i
  frame : Frame [outputR origin, workRegion origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  ok : Ok sboxCfg s
  reads : ∀ offset, offset + 4 ≤ keyLength s →
    InRegions (s.rd ++ s.wr) (addr32 (keyArg s) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 →
    InRegions s.wr (addr32 (scheduleArg s) + BitVec.ofNat 64 offset) 4
  argRead : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argOutput : (⟨argAddr s 0, 16⟩ : Region).Disjoint (outputR s)
  argWork : (⟨argAddr s 0, 16⟩ : Region).Disjoint (workRegion s)
  keyOutput : (keyR s).Disjoint (outputR s)
  keyWork : (keyR s).Disjoint (workRegion s)
  outputWork : (outputR s).Disjoint (workRegion s)
  valid : Spec.TripleDes.validKey (keyLength s)
  keyFit : (keyArg s).toNat + keyLength s ≤ 2 ^ 32
  outputFit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Components.keyArg {origin s : State} {done : Nat} (h : Components origin s done) :
    keyArg s = keyArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 1) 32 = _
  rw [← argument_word s 0, h.args 0 (by decide), argument_word origin 0]
  rfl

theorem Components.scheduleArg {origin s : State} {done : Nat} (h : Components origin s done) :
    scheduleArg s = Key.scheduleArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 3) 32 = _
  rw [← argument_word s 2, h.args 2 (by decide), argument_word origin 2]
  rfl

theorem Permissions.congr {s t : State} (hp : Permissions s)
    (args : ∀ i < 4, arg t i = arg s i) (bp : t.gpr .ebp = s.gpr .ebp)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Permissions t := by
  have key : keyArg t = keyArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 1) 32 = _
    rw [← argument_word t 0, args 0 (by decide), argument_word s 0]
    rfl
  have output : scheduleArg t = scheduleArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 3) 32 = _
    rw [← argument_word t 2, args 2 (by decide), argument_word s 2]
    rfl
  have len : keyLength t = keyLength s := by unfold keyLength; rw [args 1 (by decide)]
  have work : workRegion t = workRegion s := by unfold workRegion; rw [bp]
  have argBase : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  refine ⟨hp.ok.congr bp bp rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro off ho; rw [rd, wr, key]; exact hp.reads off (by rwa [len] at ho)
  · intro off ho; rw [wr, output]; exact hp.writes off ho
  · intro i hi; rw [rd, wr, sp]; exact hp.argRead i hi
  · rw [argBase, outputR, output]; exact hp.argOutput
  · rw [argBase, work]; exact hp.argWork
  · rw [keyR, key, len, outputR, output]; exact hp.keyOutput
  · rw [keyR, key, len, work]; exact hp.keyWork
  · rw [outputR, output, work]; exact hp.outputWork
  · rw [len]; exact hp.valid
  · rw [key, len]; exact hp.keyFit
  · rw [output]; exact hp.outputFit
  · rw [sp]; exact hp.spFit

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (keyLength origin) c = 8 * c) :
    WP isa (Impl.TripleDes.X86.Key.component (8 * c) c) s (Components origin · (c + 1)) := by
  have offBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offBound
  have hok : Ok sboxCfg s := hp.ok.congr hs.bp hs.bp hs.rd hs.wr
  have kfit : (keyArg s).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.keyArg]; omega_using [hp.keyFit, offBound]
  have sfit : (scheduleArg s + BitVec.ofNat 32 (128 * c)).toNat + 128 ≤ 2 ^ 32 := by
    rw [hs.scheduleArg, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc] : 128 * c < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hp.outputFit, hc] : (Key.scheduleArg origin).toNat + 128 * c < 2 ^ 32)]
    omega_using [hp.outputFit, hc]
  have args : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead
  have reads : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (8 * c + 4 * t)) 4 := by
    intro t ht
    change InRegions (s.rd ++ s.wr) (addr32 (keyArg s + BitVec.ofNat 32 (8 * c + 4 * t))) 4
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound, ht]), hs.rd, hs.wr]
    exact hp.reads _ (by omega_using [offBound, ht])
  have writes : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * c)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    intro j hj t ht
    rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
      Offset.add_ofNat_add_ofNat, hs.wr]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  have componentSub : Region.Sub
      (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))) (outputR origin) := by
    rw [scheduleRegion, hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])]
    exact Offset.sub_base _ (by omega_using [hc])
  have work : workRegion s = workRegion origin := by unfold workRegion; rw [hs.bp]
  have dis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))).Disjoint (workRegion s) := by
    rw [work]; exact hp.outputWork.sub_left componentSub
  apply WP.mono (component_ok s (8 * c) c hok kfit sfit args reads writes dis)
  intro t ht
  have frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (128 * c), 128⟩,
      workRegion origin] s.mem t.mem := by
    have h := ht.frame
    rw [work, scheduleRegion, hs.scheduleArg,
      VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])] at h
    exact h
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 ht.frame ht.sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr
      rw [List.mem_cons, List.mem_singleton] at hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]
      rcases hr with rfl | rfl
      · exact hp.argOutput.sub_right componentSub
      · rw [work]; exact hp.argWork)
  have key : Spec.TripleDes.blockAt s.mem (keyAddr s (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (addr32 (Key.keyArg origin) + BitVec.ofNat 64 (8 * c)) := by
    change Spec.TripleDes.blockAt s.mem (addr32 (keyArg s + BitVec.ofNat 32 (8 * c))) = _
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound])]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp.keyOutput.sub_left (Offset.sub_base _ offBound)
    · obtain rfl := List.mem_singleton.mp hr
      exact hp.keyWork.sub_left (Offset.sub_base _ offBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (ht.frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
        Offset.add_ofNat_add_ofNat, key] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have keySub : Region.Sub ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩ (outputR origin) :=
        Offset.sub_base _ (by omega_using [before, hc, hj])
      have hmem := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) k j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩) (Region.contains_self _ _) (by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Offset.disjoint _ (by omega_using [before, hj])
              (by omega_using [before, hc, hj]) (by omega_using [hc])
          · obtain rfl := List.mem_singleton.mp hr
            exact hp.outputWork.sub_left keySub) (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨outputR origin, by simp, componentSub⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨workRegion origin, by simp, by rw [work]; exact fun _ h => h⟩

theorem copyThirdStep_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : keyLength origin = 16) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (Components origin · 3) := by
  have fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32 := by rw [hs.scheduleArg]; exact hp.outputFit
  have reads : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.X86.addr (scheduleArg s) (4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.rd, hs.wr]
    obtain ⟨r, hr, hc⟩ := hp.writes (4 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 32, InRegions s.wr (VG.X86.addr (scheduleArg s) (256 + 4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.wr]
    exact hp.writes _ (by omega_using [hi])
  have ar : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead 3 (by decide)
  apply WP.mono (copyThird_ok s fit ar reads writes)
  intro t ht
  have frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame; rw [hs.scheduleArg] at h; exact h
  have sub : Region.Sub ⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩ (outputR origin) :=
    Offset.sub_base _ (by decide)
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide) (by decide)
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 frame sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]; exact hp.argOutput.sub_right sub)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide) (by decide)).trans hs.bp, sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 2 =
          componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 0 := by rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.scheduleArg] at h
      change t.mem.readW (addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have hm := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) c j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) c j, 8⟩) (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint _ (by omega_using [before, hj])
            (by omega_using [before, hj]) (by decide)) (by decide)
      exact hm.trans (hs.keys c before j hj)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, sub⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (addr32 (Key.scheduleArg origin)) =
      VG.Proof.TripleDes.expandedMemory origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (addr32 (Key.scheduleArg origin)) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.X86.Key
