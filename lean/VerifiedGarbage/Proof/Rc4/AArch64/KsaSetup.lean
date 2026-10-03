import VerifiedGarbage.Proof.Rc4.AArch64.KsaGroup

/-!
# The key schedule's setup

`ksaSetup_ok`: the setup saves the callee-saved vector registers it uses,
leaves the constants, the identity table in `v16`–`v31` (lane numbers, and
their XORs with 64, 128 and 192), `j = 0`, `S[0] = 0`, the key pointer and
length, sixteen groups to go and the base `0`: the first group's `KsaInv`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ident_xor : ∀ q < 4, laneNums q ^^^ bc 64#8 = laneNums (q + 4) ∧
    laneNums q ^^^ bc 128#8 = laneNums (q + 8) ∧ laneNums (q + 4) ^^^ bc 128#8 = laneNums (q + 12) := by
  decide +kernel

/-- The identity table's code, written out. -/
def identCode : List Instr :=
  [.vop (.mov .v16 .v8), .vop (.mov .v17 .v9), .vop (.mov .v18 .v10), .vop (.mov .v19 .v11),
   eorV .v20 .v8 .v12, eorV .v21 .v9 .v12, eorV .v22 .v10 .v12, eorV .v23 .v11 .v12,
   eorV .v24 .v8 .v13, eorV .v25 .v9 .v13, eorV .v26 .v10 .v13, eorV .v27 .v11 .v13,
   eorV .v28 .v20 .v13, eorV .v29 .v21 .v13, eorV .v30 .v22 .v13, eorV .v31 .v23 .v13]

theorem identCode_eq :
    (List.range 4).map (fun r => .vop (.mov (treg r) (lanes r))) ++
    (List.range 4).map (fun r => eorV (treg (4 + r)) (lanes r) c64) ++
    (List.range 4).map (fun r => eorV (treg (8 + r)) (lanes r) c128) ++
    (List.range 4).map (fun r => eorV (treg (12 + r)) (treg (4 + r)) c128) = identCode := by
  decide

theorem ident_ok {s : State} (hk : Consts s) :
    WP isa (.block identCode) s fun t =>
      (∀ q < 16, t.v (treg q) = laneNums q) ∧ (∀ v, NotTable v → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have l0 : s.v .v8 = laneNums 0 := hk.lns 0 (by decide)
  have l1 : s.v .v9 = laneNums 1 := hk.lns 1 (by decide)
  have l2 : s.v .v10 = laneNums 2 := hk.lns 2 (by decide)
  have l3 : s.v .v11 = laneNums 3 := hk.lns 3 (by decide)
  have k64 : s.v .v12 = bc 64 := hk.c64
  have k128 : s.v .v13 = bc 128 := hk.c128
  have x0 := ident_xor 0 (by decide)
  have x1 := ident_xor 1 (by decide)
  have x2 := ident_xor 2 (by decide)
  have x3 := ident_xor 3 (by decide)
  simp only [Nat.reduceAdd] at x0 x1 x2 x3
  unfold identCode eorV
  rrun [l0, l1, l2, l3, k64, k128, x0.1, x0.2.1, x0.2.2, x1.1, x1.2.1, x1.2.2, x2.1, x2.2.1,
    x2.2.2, x3.1, x3.2.1, x3.2.2]
  refine ⟨fun q hq => ?_, fun v hv => ?_, ?_⟩
  · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
      q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [treg]
  · have ne (a : Nat) (ha : a < 16) : v ≠ treg a := (hv a ha).symm
    have n0 : v ≠ .v16 := ne 0 (by decide)
    have n1 : v ≠ .v17 := ne 1 (by decide)
    have n2 : v ≠ .v18 := ne 2 (by decide)
    have n3 : v ≠ .v19 := ne 3 (by decide)
    have n4 : v ≠ .v20 := ne 4 (by decide)
    have n5 : v ≠ .v21 := ne 5 (by decide)
    have n6 : v ≠ .v22 := ne 6 (by decide)
    have n7 : v ≠ .v23 := ne 7 (by decide)
    have n8 : v ≠ .v24 := ne 8 (by decide)
    have n9 : v ≠ .v25 := ne 9 (by decide)
    have n10 : v ≠ .v26 := ne 10 (by decide)
    have n11 : v ≠ .v27 := ne 11 (by decide)
    have n12 : v ≠ .v28 := ne 12 (by decide)
    have n13 : v ≠ .v29 := ne 13 (by decide)
    have n14 : v ≠ .v30 := ne 14 (by decide)
    have n15 : v ≠ .v31 := ne 15 (by decide)
    simp [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]
  · simp [State.setV]

theorem saveK_ok (s : State) :
    WP isa (.block (save false)) s fun t =>
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ≠ .x10 → g ≠ .x11 → g ≠ .x14 → g ≠ .x15 → g ≠ .x16 → g ≠ .x17 → t.gpr g = s.gpr g) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold save saved
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil]
  refine ⟨fun p hp => ?_, fun g a b c d e f => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [a, b, c, d, e, f]
  · simp [State.write]

/-- The registers the key schedule's setup writes. -/
def ksaRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x14, .x15, .x16, .x17]

/-- The key schedule's globals for the call from `s`, entering the loop in `t`. -/
def kglob (s t : State) : KGlob := ⟨s.gpr .x0, (s.gpr .x1).toNat, s.mem, t⟩

theorem ident_get {k : Nat} (hk : k < 256) :
    (Vector.ofFn fun i : Fin 256 => BitVec.ofNat 8 i.val).getD (BitVec.ofNat 8 (0 + k)).toNat 0 =
      BitVec.ofNat 8 k := by
  rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp [Vector.getD, hk]
  apply BitVec.eq_of_toNat_eq
  show k = k % 2 ^ 8
  omega

theorem scheduleSetup_eq : scheduleSetup = save false ++ (constants ++ (identCode ++
    ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0,
      .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr))) := by
  rw [← identCode_eq]; simp only [scheduleSetup, List.append_assoc]

theorem tailK_ok (c : State) :
    WP isa (.block ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0,
      .addImm .x .x5 .x1 0, .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr)) c fun t =>
      t.v (dq 0) = 0 ∧ t.v si = 0 ∧ (∀ v, v ≠ .v0 → v ≠ .v4 → t.v v = c.v v) ∧
      t.gpr .x7 = c.gpr .x0 ∧ t.gpr .x5 = c.gpr .x1 ∧ t.gpr .x4 = 16#64 ∧ t.gpr .x8 = 0#64 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → t.gpr r = c.gpr r) ∧
      t.mem = c.mem ∧ t.rd = c.rd ∧ t.wr = c.wr ∧ t.sp = c.sp := by
  have d0 : dq 0 = .v0 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, s4]
  refine ⟨fun v a b => by simp [a, b], fun r a b c d => by simp [a, b, c, d], ?_⟩
  simp [State.write, State.setV]

theorem ksaSetup_ok {s : State} (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa (.block scheduleSetup) s fun t =>
      (kglob s t).Ok ∧ KsaInv (kglob s t) 0 0 t ∧
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r) ∧ t.v .v14 = s.v .v14 ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [scheduleSetup_eq, WP.block_append_iff]
  refine WP.mono (saveK_ok s) fun a ⟨asv, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok a) fun b ⟨bc', bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ident_ok bc') fun c ⟨ct, cv, cg, cm, crd, cwr, csp⟩ => ?_
  refine WP.mono (tailK_ok c) fun t ⟨tj, tsi, tv, t7, t5, t4, t8, tg, tm, trd, twr, tsp⟩ => ?_
  have hL1 := hL.1
  have gk : ∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r := fun r hr => by
    have n : ∀ g ∈ ksaRegs, r ≠ g := fun g hg e => hr (e ▸ hg)
    rw [tg r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)), cg,
      bg r (n _ (by decide)) (n _ (by decide)),
      ag r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide))
        (n _ (by decide))]
  have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide)
  have t1 : t.gpr .x1 = s.gpr .x1 := gk _ (by decide)
  have tvt : ∀ q < 16, t.v (treg q) = laneNums q := fun q hq => by
    rw [tv _ ((show NotTable .v0 by decide) q hq) ((show NotTable .v4 by decide) q hq), ct q hq]
  have tcon : Consts t := bc'.congr fun r hr => by
    rw [tv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      cv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have tb : ∀ k < 256, tbyte t.v k = BitVec.ofNat 8 k := fun k hk => by
    rw [tbyte, tvt _ (by omega), laneNums, vbyte_ofVBytes _ (by omega)]
    congr 1; omega
  have keep : ∀ v, v ≠ .v0 → v ≠ .v4 → NotTable v → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 →
      v ≠ .v11 → v ≠ .v12 → v ≠ .v13 → t.v v = s.v v := fun v h0 h4 ht h7 h8 h9 h10 h11 h12 h13 => by
    rw [tv v h0 h4, cv v ht, bv v h7 h8 h9 h10 h11 h12 h13, av]
  have hok : (kglob s t).Ok := by
    refine ⟨hL.1, hL.2, t0, ?_, ?_⟩
    · show t.gpr .x1 = _
      rw [t1]; simp [kglob]
    · show InRegions (t.rd ++ t.wr) _ _
      rw [trd, twr, crd, cwr, brd, bwr, ard, awr]; exact hk
  refine ⟨hok, ?_, fun p hp => ?_, gk, keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), by rw [tm, cm, bm, am], by rw [trd, crd, brd, ard],
    by rw [twr, cwr, bwr, awr], by rw [tsp, csp, bsp, asp]⟩
  · exact {
      consts := tcon
      table := fun k hk => by rw [tb k hk]; exact (ident_get hk).symm
      j := by rw [tj, Nat.add_zero, schedule_zero]; decide
      si := by rw [tsi, tb 0 (by decide)]; rfl
      x7 := by rw [t7, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; simp [kglob]
      x5 := by
        rw [t5, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        simp [kglob]
      x8 := by rw [t8]
      x4 := by rw [t4]
      gpr := fun _ _ _ _ _ _ => rfl
      vkept := fun _ _ => rfl
      mem := by rw [tm, cm, bm, am]; rfl
      rd := rfl
      wr := rfl
      sp := rfl }
  · have ⟨h6, h7⟩ : p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by revert p; decide
    have ⟨h4, h5, h8⟩ : p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x8 := by revert p; decide
    rw [tg _ h4 h5 h7 h8, cg, bg _ h6 h7, asv p hp]

end VG.Proof.Rc4.AArch64
