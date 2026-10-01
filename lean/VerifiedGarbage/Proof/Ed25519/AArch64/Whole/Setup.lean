import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def value (E : Addr) (m : Mem) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => E + BitVec.ofNat 64 d
  | .caller j d => m.read (E + BitVec.ofNat 64 (256 + 8 * j)) 8 + BitVec.ofNat 64 d

def valid : Value → Prop
  | .const n => n < 65536
  | .frame d => d < 4096
  | .caller j d => j < 6 ∧ d < 4096

structure SetupStep (rs : List Reg) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  vec : t.v = s.v
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : SetupStep [] s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem SetupStep.trans {rs rs' : List Reg} {s t u : State}
    (h : SetupStep rs s t) (h' : SetupStep rs' t u) : SetupStep (rs ++ rs') s u := by
  refine ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    h'.mem.trans h.mem, h'.vec.trans h.vec, ?_⟩
  intro r hr
  exact (h'.regs r (fun hmem => hr (List.mem_append_right _ hmem))).trans
    (h.regs r (fun hmem => hr (List.mem_append_left _ hmem)))

theorem setArg_ok {s : State} {E : Addr} {r : Reg} {v : Value}
    (he : s.sp = E) (hv : valid v)
    (hr : ∀ j d, v = .caller j d → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (setArg r v)) s fun t => SetupStep [r] s t ∧ t.gpr r = value E s.mem v := by
  cases v with
  | const n =>
    change n < 65536 at hv
    have hn : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    apply WP.of_runBlock
    simp only [setArg, value, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, Nat.mul_zero, Nat.zero_lt_succ, ite_true, BitVec.shiftLeft_zero,
      hn, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)
    · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  | frame d =>
    change d < 4096 at hv
    apply WP.of_runBlock
    simp only [setArg, value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hv, ite_true, he, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)
    · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  | caller j d =>
    obtain ⟨hj, hd⟩ := hv
    have ha : (256 + 8 * j) % 8 = 0 ∧ 256 + 8 * j < 32768 := by omega
    have hr' := hr j d rfl
    apply WP.of_runBlock
    simp only [setArg, value, runBlock_cons, runStep_some, runBlock_nil, exec,
      ha.1, ha.2, and_self, hd, ite_true, he, State.load, hr', Option.map_some, State.read,
      Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      have hqr : q ≠ r := by simpa using hq
      rw [RegUpd.gpr_write_of_ne _ _ _ hqr, RegUpd.gpr_write_of_ne _ _ _ hqr]
    · exact True.intro

/-- Setup does not touch memory and writes each destination exactly once. -/
theorem setup_ok {s : State} {E : Addr} {args : List (Reg × Value)}
    (he : s.sp = E) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (setup args)) s fun t => SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [setup, List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r,v) List.mem_cons_self
    refine WP.mono (setArg_ok he hv0 ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs r hn.1).trans hval
    · rw [hvals p hp, hu.mem]

theorem Ctx.setup {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : Ctx E g v m₀ rd wr s)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2)
    (hr : ARGS E ∈ rd)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => Ctx E g v m₀ rd wr t ∧
      t.mem = s.mem ∧ ∀ p ∈ args, t.gpr p.1 = value E s.mem p.2 := by
  refine WP.mono (setup_ok hc.sp hn hv ?_) fun t ⟨ht, hvals⟩ => ?_
  · intro j hj
    rw [hc.rd, hc.wr]
    refine ⟨ARGS E, List.mem_append_left _ hr, ?_⟩
    have ha : E + BitVec.ofNat 64 (256 + 8 * j) =
        E + 256 + BitVec.ofNat 64 (8 * j) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [ha]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.vec ht.mem, ht.mem, hvals⟩
  intro r hpres _
  apply ht.regs
  intro hm
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  exact hregs p hp (heq ▸ hpres)

end VG.Proof.Ed25519.AArch64.Whole
