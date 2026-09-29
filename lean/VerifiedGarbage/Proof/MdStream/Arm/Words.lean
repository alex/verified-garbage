import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: length fields and digests

Untrusted: everything here is checked by Lean. What the length fields
(`len64`) and digests (`out32`) of `Impl/MdStream/Arm.lean` write, for the
hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.Arm

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame shl3 bits8)

/-! ## Byte order -/

theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then rev x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · simp [bytes32, List.range_succ]
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · refine byte_ext fun i hi => ?_
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact absurd hi (by omega)
        | (simp only [rev, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp)

theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then rev x else x) = writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes32_store]; rfl

theorem writeW_le (m : Mem) (a : Addr) (x : BitVec 32) :
    m.writeW a x = writeBytes m a (bytes32 false x) := writeW32 m a false x

theorem writeW_be (m : Mem) (a : Addr) (x : BitVec 32) :
    m.writeW a (rev x) = writeBytes m a (bytes32 true x) := writeW32 m a true x

/-- A 64-bit word's bytes are its halves'. -/
theorem bytes64_halves (be : Bool) (hi lo : BitVec 32) :
    bytes64 be (hi ++ lo) =
      if be then bytes32 true hi ++ bytes32 true lo else bytes32 false lo ++ bytes32 false hi := by
  cases be
  · simp only [bytes64, bytes32, Bool.false_eq_true, ite_false, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · refine byte_ext fun i hi => ?_
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact absurd hi (by omega)
        | (simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp)
  · simp only [bytes64, bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · refine byte_ext fun i hi => ?_
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact absurd hi (by omega)
        | (simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp)

/-! ## Regions -/

theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [show a + BitVec.ofNat 64 off - R.base = (a - R.base) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

/-- `len64 d be` stores `8 · (r5:r4)` at `r0 + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} (hd : d + 4 < 4096)
    (hfit : (s.gpr .r0).toNat + d + 8 ≤ 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) 8) :
    WP isa (.block (len64 d be)) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r5 ++ s.gpr .r4).toNat))) := by
  have hv : BitVec.ofNat 64 (8 * (s.gpr .r5 ++ s.gpr .r4).toNat) =
      (s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29) ++ s.gpr .r4 <<< 3 := by rw [bits8, shl3]
  have a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr (s.gpr .r0) + BitVec.ofNat 64 d :=
    addr_off (by omega)
  have a4 : State.addr (s.gpr .r0 + BitVec.ofNat 32 (d + 4)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4 := by
    rw [addr_off (by omega), add_ofNat]
  have o0 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) 4 := by
    simpa using InRegions.offset hout (off := 0) (m := 4) (by omega) (by omega)
  have o4 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) 4 :=
    InRegions.offset hout (by omega) (by omega)
  have hw : ∀ (m : Mem) (xs ys : List Byte), xs.length = 4 → ys.length = 4 →
      writeBytes (writeBytes m (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) xs)
        (State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) ys =
      writeBytes m (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) (xs ++ ys) := by
    intro m xs ys hx hy
    rw [← writeBytes_append _ _ _ _ (by omega), hx]
  cases be
  · simp only [len64, Bool.false_eq_true, ite_false]
    refine wp_mov (op2_lsl (by decide)) fun s₁ u₁ => wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
      (by omega) (by rw [u₁.other _ (by decide), a0]) (by rw [u₁.wr]; exact o0) fun s₂ g₂ => ?_
    refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => wp_orr (op2_lsr (by decide)) fun s₄ u₄ =>
      wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), a4])
        (by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr]; exact o4) fun s₅ g₅ => WP.block_nil
          ⟨fun r h => by rw [g₅.gpr, u₄.other r h, u₃.other r h, g₂.gpr, u₁.other r h],
            by rw [g₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd], by rw [g₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr],
            by rw [g₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp], ?_⟩
    have e₄ : s₄.gpr .r9 = s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29 := by
      rw [u₄.gpr, u₃.gpr, u₃.other .r4 (by decide), g₂.gpr, u₁.other .r5 (by decide), u₁.other .r4 (by decide)]
    rw [g₅.mem, e₄, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, hv, bytes64_halves]
    simp only [Bool.false_eq_true, ite_false]
    rw [writeW_le, writeW_le, hw _ _ _ (bytes32_length _ _) (bytes32_length _ _)]
  · simp only [len64, ite_true]
    refine wp_mov (op2_lsl (by decide)) fun s₁ u₁ => wp_orr (op2_lsr (by decide)) fun s₂ u₂ =>
      wp_rev fun s₃ u₃ => wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
      (by omega) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), a0])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o0) fun s₄ g₄ => ?_
    refine wp_mov (op2_lsl (by decide)) fun s₅ u₅ => wp_rev fun s₆ u₆ =>
      wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), a4])
        (by rw [u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o4) fun s₇ g₇ => WP.block_nil
          ⟨fun r h => by rw [g₇.gpr, u₆.other r h, u₅.other r h, g₄.gpr, u₃.other r h, u₂.other r h,
              u₁.other r h],
            by rw [g₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd],
            by rw [g₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr],
            by rw [g₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_⟩
    have e₃ : s₃.gpr .r9 = rev (s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29) := by
      rw [u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .r4 (by decide)]
    have e₆ : s₆.gpr .r9 = rev (s.gpr .r4 <<< 3) := by
      rw [u₆.gpr, u₅.gpr, g₄.gpr, u₃.other .r4 (by decide), u₂.other .r4 (by decide), u₁.other .r4 (by decide)]
    rw [g₇.mem, e₆, u₆.mem, u₅.mem, g₄.mem, e₃, u₃.mem, u₂.mem, u₁.mem, hv, bytes64_halves]
    simp only [ite_true]
    rw [writeW_be, writeW_be, hw _ _ _ (bytes32_length _ _) (bytes32_length _ _)]

/-! ## The digest -/

/-- `out32 n be` writes the `n` 32-bit words at `r0` to `r6`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (f₀ : (s₀.gpr .r0).toNat + 4 * n ≤ 2 ^ 32) (f₆ : (s₀.gpr .r6).toNat + 4 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r0)) (4 * n))
    (hout : InRegions s₀.wr (State.addr (s₀.gpr .r6)) (4 * n))
    (hd : Region.Disjoint ⟨State.addr (s₀.gpr .r0), 4 * n⟩ ⟨State.addr (s₀.gpr .r6), 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .r9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (State.addr (s₀.gpr .r6))
        ((List.range n).flatMap fun k =>
          bytes32 be (s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 32)) := by
  let f : Nat → List Byte := fun k =>
    bytes32 be (s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 32)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 4 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes32_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .r9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        [.ldr .r9 .r0 (4 * k)] ++ (if be then [.rev .r9 .r9] else []) ++ [.str .r9 .r6 (4 * k)]))
        s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range,
      List.append_assoc, List.append_assoc]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 4 * (n - (j + 1)) + 4 ≤ 4 * n := by omega
    have a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * (n - (j + 1)))) =
        State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1))) := by
      rw [g _ (by decide)]; exact addr_off (by omega)
    have a6 : ∀ t : State, t.gpr .r6 = s₀.gpr .r6 →
        State.addr (t.gpr .r6 + BitVec.ofNat 32 (4 * (n - (j + 1)))) =
          State.addr (s₀.gpr .r6) + BitVec.ofNat 64 (4 * (n - (j + 1))) :=
      fun t ht => by rw [ht]; exact addr_off (by omega)
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 =
        s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨State.addr (s₀.gpr .r6), 4 * n⟩) ?_).readW
        (r := ⟨State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1))), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset hoff (by omega))
    have hmem : ∀ (t : State), t.mem = s.mem →
        t.mem.writeW (State.addr (s₀.gpr .r6) + BitVec.ofNat 64 (4 * (n - (j + 1))))
          (if be then rev (s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32)
            else s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32) =
        writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range (n - j)).flatMap f) := by
      intro t ht
      rw [ht, writeW32, hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton,
        ← writeBytes_append _ _ _ _ (by rw [hflat, bytes32_length]; omega), hflat]
    refine wp_ldr (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) (by omega) a0
      (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    cases be
    · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
      refine wp_str (by omega) (a6 s₁ (by rw [u₁.other _ (by decide), g _ (by decide)]))
        (by rw [u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ => ?_
      refine ih (by omega) s₂ (fun r h => by rw [g₂.gpr, u₁.other r h, g r h]) (by rw [g₂.rd, u₁.rd, rd])
        (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
      rw [g₂.mem, u₁.gpr]
      exact hmem s₁ u₁.mem
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine wp_rev fun s₂ u₂ => wp_str (by omega) (a6 s₂ (by rw [u₂.other _ (by decide),
        u₁.other _ (by decide), g _ (by decide)])) (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega))
        fun s₃ g₃ => ?_
      refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
        (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
      rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr]
      exact hmem s₁ u₁.mem

end VG.Proof.MdStream.Arm
