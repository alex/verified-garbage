import VerifiedGarbage.Proof.Rc4.AArch64.KsaStep

/-!
# The key schedule's groups

`ksaLane_ok`: a lane of the key schedule is a scheduling round;
`ksaGroup_ok`: sixteen lanes and the rotation take the group with base `B`
to the next, with base `B + 16`; `ksaLoop_ok`: sixteen groups take the
identity table to the key schedule, its registers back where they started.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The key schedule's globals: the key at `K` of `L` bytes in the memory
`M`, and the state `s₀` that the setup leaves. -/
structure KGlob where
  K : Addr
  L : Nat
  M : Mem
  s₀ : State

def KGlob.key (g : KGlob) : List Byte := bytesAt g.M g.K g.L

structure KGlob.Ok (g : KGlob) : Prop where
  pos : 0 < g.L
  le : g.L ≤ 256
  x0 : g.s₀.gpr .x0 = g.K
  x1 : g.s₀.gpr .x1 = BitVec.ofNat 64 g.L
  key : InRegions (g.s₀.rd ++ g.s₀.wr) g.K g.L

/-- Lane `l` of the group whose base is `B`: `B + l` rounds done. -/
structure KsaInv (g : KGlob) (B l : Nat) (s : State) : Prop where
  consts : Consts s
  table : TableIn s B (schedulePrefix g.key (B + l)).1
  j : s.v (dq 0) = bc ((schedulePrefix g.key (B + l)).2 - bB B)
  si : s.v si = bc (tbyte s.v l)
  x7 : s.gpr .x7 = g.K + BitVec.ofNat 64 ((B + l) % g.L)
  x5 : s.gpr .x5 = BitVec.ofNat 64 (g.L - (B + l) % g.L)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  x4 : s.gpr .x4 = BitVec.ofNat 64 (16 - B / 16)
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  vkept : ∀ r, r ∉ stepRegs → s.v r = g.s₀.v r
  mem : s.mem = g.M
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

theorem sub_add_comm8 (x y z : BitVec 8) : x - y + z = x + z - y := by bv_omega

theorem ksaLane_ok {g : KGlob} (hg : g.Ok) {B l : Nat} (hl : l < 16) (hB : B + l < 256) {s : State}
    (h : KsaInv g B l s) :
    WP isa (.seq keyByte (.block (swapStep false l))) s (KsaInv g B (l + 1)) := by
  have h0 : s.gpr .x0 = g.K := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x0]
  have h1 : s.gpr .x1 = BitVec.ofNat 64 g.L := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x1]
  have hkey : InRegions (s.rd ++ s.wr) g.K g.L := by rw [h.rd, h.wr]; exact hg.key
  refine WP.seq (WP.mono (keyByte_ok hg.pos (by have := hg.le; omega) h0 h1 h.x7 h.x5 hkey h.j)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  have hkb : s.mem (g.K + BitVec.ofNat 64 ((B + l) % g.L)) =
      g.key.getD ((B + l) % g.key.length) 0 := by
    rw [KGlob.key, bytes_length, bytes_get _ _ _ _ (Nat.mod_lt _ hg.pos), h.mem]
  have aj' : a.v (dq 0) = bc ((schedulePrefix g.key (B + l)).2 +
      g.key.getD ((B + l) % g.key.length) 0 - bB B) := by rw [aj, hkb, sub_add_comm8]
  have ka : Consts a := h.consts.congr fun r hr => av r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have tba : ∀ k < 256, tbyte a.v k = tbyte s.v k := fun k hk =>
    tbyte_congr (fun q hq => av _ ((show NotTable (dq 0) by decide) q hq)
      ((show NotTable .v6 by decide) q hq)) hk
  have ta : TableIn a B (schedulePrefix g.key (B + l)).1 := fun k hk => by
    rw [tba k hk]; exact h.table k hk
  have sia : a.v si = bc (tbyte a.v l) := by
    rw [av _ (by decide) (by decide), h.si, tba l (by omega)]
  obtain ⟨t, run, tt, tj, tsi, to⟩ := ksaSwap_ok hl rfl hB ka ta aj' sia
  refine WP.of_runBlock ⟨t, run, ?_⟩
  have tg := to.gpr
  exact {
    consts := consts_of_only ka to
    table := tt
    j := tj
    si := tsi
    x7 := by rw [tg, a7]; rfl
    x5 := by rw [tg, a5]; rfl
    x8 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x8
    x4 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x4
    gpr := fun r r4 r5 r6 r7 r8 => by rw [tg, ag r r5 r6 r7]; exact h.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [to.2 r hr, av r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))]
      exact h.vkept r hr
    mem := by rw [to.mem, am]; exact h.mem
    rd := by rw [to.rd, ard]; exact h.rd
    wr := by rw [to.wr, awr]; exact h.wr
    sp := by rw [to.sp, asp]; exact h.sp }

theorem ksaLanes_ok {g : KGlob} (hg : g.Ok) {B : Nat} (hB : B + 16 ≤ 256) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : KsaInv g B 0 s) : WP isa (scheduleLanes n) s (KsaInv g B n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun t ht => ksaLane_ok hg (by omega) (by omega) ht)

theorem subX4_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x4 1]) s fun t =>
      t.gpr .x4 = s.gpr .x4 - 1 ∧ (∀ r, r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rrun
  refine ⟨fun r hr => by simp [hr], by simp [State.write]⟩

theorem ksaGroup_ok {g : KGlob} (hg : g.Ok) {B : Nat} (hB16 : B % 16 = 0) (hB : B < 256) {s : State}
    (h : KsaInv g B 0 s) : WP isa scheduleGroup s (KsaInv g (B + 16) 0) := by
  apply WP.seq (WP.mono (ksaLanes_ok hg (by omega) (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok false h₁.consts h₁.j (NB := 0) fun e => absurd e (by decide))
    fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  refine WP.mono (subX4_ok t) fun u ⟨u4, ug, uv, um, urd, uwr, usp⟩ => ?_
  have tbu : tbyte u.v = tbyte t.v := by rw [uv]
  exact {
    consts := h₁.consts.congr fun r hr => by
      rw [uv]; exact vv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    table := fun k hk => by
      rw [tbu, tab k hk, h₁.table _ (by omega), ofNat_wrap]
    j := by rw [uv, j, byte_shift]
    si := by
      rw [uv, vv _ (by decide), h₁.si, tab 0 (by decide)]
    x7 := by
      rw [ug _ (by decide), gg _ (by decide), h₁.x7, show B + 16 + 0 = B + 16 from rfl]
    x5 := by rw [ug _ (by decide), gg _ (by decide), h₁.x5]
    x8 := by
      rw [ug _ (by decide), x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
        BitVec.ofNat_add_ofNat]
    x4 := by
      rw [u4, gg _ (by decide), h₁.x4, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1; omega
    gpr := fun r r4 r5 r6 r7 r8 => by rw [ug r r4, gg r r8]; exact h₁.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [uv]
      by_cases hn : r = negBase
      · subst hn; simp only [Bool.false_eq_true, ite_false] at nb; rw [nb]; exact h₁.vkept _ hr
      · rw [vv r (by
          simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
            not_and]
          exact ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
            fun a ha e => hr (e ▸ treg_step a ha)⟩)]
        exact h₁.vkept r hr
    mem := by rw [um, m]; exact h₁.mem
    rd := by rw [urd, rd]; exact h₁.rd
    wr := by rw [uwr, wr]; exact h₁.wr
    sp := by rw [usp, sp]; exact h₁.sp }

/-- A group about to start, `m` groups before the end. -/
def KLoopInv (g : KGlob) (m : Nat) (s : State) : Prop :=
  ∃ B, m = 16 - B / 16 ∧ B % 16 = 0 ∧ B < 256 ∧ KsaInv g B 0 s

theorem ksaLoop_ok {g : KGlob} (hg : g.Ok) (m : Nat) {s : State} (h : KLoopInv g m s) :
    WP isa (.loop scheduleGroup (.nonzero .x .x4)) s (KsaInv g 256 0) := by
  refine WP.loop (M := isa) (KLoopInv g) ?_ m s h
  intro m s ⟨B, hm, hB16, hB, h⟩
  refine WP.mono (ksaGroup_ok hg hB16 hB h) fun t ht => ?_
  have flag := eval_nonzero' t .x4 ht.x4 (by omega)
  by_cases hend : B + 16 = 256
  · left
    exact ⟨by rw [flag]; simp [hend], hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega, 16 - (B + 16) / 16, by omega, B + 16, rfl, by omega,
      by omega, ht⟩

end VG.Proof.Rc4.AArch64
