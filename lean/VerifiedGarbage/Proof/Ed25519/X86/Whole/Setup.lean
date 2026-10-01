import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def value (E : BitVec 32) (m : Mem) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => E + BitVec.ofNat 32 d
  | .caller i d => m.readW (addr E (260 + 4 * i)) 32 + BitVec.ofNat 32 d

def valid (n : Nat) : Value → Prop
  | .caller i _ => i < n
  | _ => True

structure SetupStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .eax → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : SetupStep s s := ⟨rfl, rfl, fun _ _ => rfl⟩
theorem SetupStep.trans {s t u : State} (h : SetupStep s t) (h' : SetupStep t u) : SetupStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => (h'.regs r hr).trans (h.regs r hr)⟩
theorem SetupStep.esp {s t : State} (h : SetupStep s t) : t.gpr .esp = s.gpr .esp := h.regs _ (by decide)

theorem put_ok {s : State} {E : BitVec 32} {slot : Nat} {v : Value}
    (he : s.gpr .esp = E)
    (hr : ∀ i d, v = .caller i d → InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hw : InRegions s.wr (addr E (4 * slot)) 4) :
    WP isa (.block (put slot v)) s fun t => SetupStep s t ∧
      t.mem = s.mem.writeW (addr E (4 * slot)) (value E s.mem v) := by
  cases v with
  | const n =>
    apply WP.of_runBlock
    simp only [put, load, value, at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.store32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      reduceCtorEq, ite_false, ite_true, he, hw, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, h, ite_false]⟩, True.intro⟩
  | frame d =>
    apply WP.of_runBlock
    simp only [put, load, value, at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      reduceCtorEq, ite_false, ite_true, he, hw, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
  | caller i d =>
    have hr' := hr i d rfl
    apply WP.of_runBlock
    simp only [put, load, value, at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store32, State.load32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      reduceCtorEq, ite_false, ite_true, he, hw, hr', Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩

theorem frame_word {s : State} {E : BitVec 32} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : FR E ∈ s.wr) {d : Nat} (hd : d + 4 ≤ 256) : InRegions s.wr (addr E d) 4 := by
  refine ⟨_, hw, ?_⟩
  rw [addr_eq (by omega_using [hf, hd])]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

theorem value_congr {E : BitVec 32} {m m' : Mem} {v : Value} {n : Nat}
    (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32) (hv : valid n v)
    (hm : Frame [⟨E.setWidth 64, 24⟩] m m') : value E m' v = value E m v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller i d =>
    change i < n at hv
    unfold value
    apply congrArg (· + BitVec.ofNat 32 d)
    rw [addr_eq (by omega_using [hf, hv])]
    refine hm.readW (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by omega_using [hv]) (by omega_using [hf, hv])

/-- Set consecutive outgoing argument words. Each instruction shape is checked
once, and the list is composed without repeating symbolic execution. -/
theorem setup_ok {s : State} {E : BitVec 32} {n start : Nat} {vs : List Value}
    (he : s.gpr .esp = E) (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hw : FR E ∈ s.wr) (hlen : start + vs.length ≤ 6)
    (hv : ∀ v ∈ vs, valid n v) :
    WP isa (.block (setup start vs)) s fun t => SetupStep s t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * vs.length⟩] s.mem t.mem ∧
      ∀ j (hj : j < vs.length), t.mem.readW (addr E (4 * (start + j))) 32 =
        value E s.mem (vs[j]'hj) := by
  induction vs generalizing s start with
  | nil =>
    exact WP.block_nil ⟨SetupStep.refl s, Frame.refl _ _, fun _ h => by cases h⟩
  | cons v vs ih =>
    rw [setup, WP.block_append_iff]
    have fit : E.toNat + 256 ≤ 2 ^ 32 := by omega_using [hf]
    have hs : start < 6 := by simp only [List.length_cons] at hlen; omega_using [hlen]
    have av : valid n v := hv v List.mem_cons_self
    refine WP.mono (put_ok he (fun i d h => by subst v; exact hr i av)
      (frame_word fit hw (by omega_using [hs]))) fun u ⟨hu, hm⟩ => ?_
    have hf24 : Frame [⟨E.setWidth 64, 24⟩] s.mem u.mem := by
      rw [hm, addr_eq (by omega_using [hf, hs])]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hs]) (by omega_using [hs]))
    refine WP.mono (ih (hu.esp.trans he) (by rw [hu.rd, hu.wr]; exact hr)
      (hu.wr ▸ hw) (by simp only [List.length_cons] at hlen; omega_using [hlen])
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))) fun t ⟨ht, ft, vt⟩ => ?_
    refine ⟨hu.trans ht, ?_, ?_⟩
    · have fs : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * (v :: vs).length⟩] s.mem u.mem := by
        rw [hm, addr_eq (by omega_using [hf, hs])]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, List.length_cons]; omega)
      refine fs.trans (Frame.sub ft ?_)
      rintro r hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub _ (by omega) (by simp; omega)
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        have keep : t.mem.readW (addr E (4 * start)) 32 = u.mem.readW (addr E (4 * start)) 32 := by
          rw [addr_eq (by omega_using [hf, hs])]
          refine ft.readW (Region.contains_self _ _) ?_ (by decide)
          rintro r hr'
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (by omega) (by simp only [List.length_cons] at hlen; omega_using [hlen])
            (by simp only [List.length_cons] at hlen; omega_using [hlen])
        rw [keep, hm, Mem.readW_writeW_self32]
      | succ j =>
        have hj' : j < vs.length := by simpa using hj
        have e : start + (j + 1) = start + 1 + j := by omega
        rw [e, vt j hj']
        exact value_congr hf (hv _ (List.mem_cons_of_mem _ (List.getElem_mem _))) hf24

theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : Ctx E g m₀ rd wr s) {n start : Nat} {vs : List Value}
    (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hlen : start + vs.length ≤ 6) (hv : ∀ v ∈ vs, valid n v) :
    WP isa (.block (setup start vs)) s fun t => Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64, 24⟩] s.mem t.mem ∧
      ∀ j (hj : j < vs.length), t.mem.readW (addr E (4 * (start + j))) 32 =
        value E s.mem (vs[j]'hj) := by
  refine WP.mono (setup_ok hc.esp hf hr (by rw [hc.wr]; exact List.mem_cons_self) hlen hv)
    fun t ⟨ht, hft, hvals⟩ => ?_
  have hf24 : Frame [⟨E.setWidth 64, 24⟩] s.mem t.mem :=
    hft.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [hlen])⟩
  refine ⟨hc.of_frame ht.rd ht.wr ht.esp ?_ hf24 ?_, hf24, hvals⟩
  · intro r hr _
    apply ht.regs
    rintro rfl
    simp [calleeSaved] at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Region.sub_prefix (by decide))

end VG.Proof.Ed25519.X86.Whole
