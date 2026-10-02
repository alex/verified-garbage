import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update

/-!
# Streaming SHA-512 on ARMv7: `finalize`

`finalize` is the generic streaming code (`Impl/MdStream/Arm.lean`), so it is
verified by the generic proof (`Proof/MdStream/Arm/Finalize.lean`) for the
SHA-512 family's instance (`Proof/Sha512/Md.lean`), given what the family's
own pieces do: its length field and digest (`shape`), that its compression
function is verified (`callee`), and that the taint analysis accepts its code.
-/

namespace VG.Proof.Sha512.Arm.Stream.Finalize

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Sha512.Arm.Stream (outW)
open VG.Impl.MdStream.Arm (len64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame write_eq_writeBytes)
open VG.Proof.Sha512.Arm (readW_lo readW_hi)
open VG.Spec.Sha512 (HashValue stateAt wordBytes)

/-! ## Words

The halves of the words of the length field and the digest
(`Proof/Sha512/Word64.lean`), for the implementation's `lo` and `hi`. -/

theorem wordBytes_split (x : BitVec 64) :
    wordBytes x = Spec.Sha256.wordBytes (hi x) ++ Spec.Sha256.wordBytes (lo x) :=
  Word64.wordBytes_split x

theorem writeW_rev (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev w) = writeBytes m a (Spec.Sha256.wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes]
  exact congrArg (writeBytes m a) (byteRev32_extract w)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 8 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 8 := fun w _ => by simp [wordBytes]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

theorem lo_shr61 (x : BitVec 64) : lo (x >>> 61) = hi x >>> 29 := Word64.lo_shr61 x

theorem hi_shr61 (x : BitVec 64) : hi (x >>> 61) = 0 := Word64.hi_shr61 x

/-! ## The length field -/

/-- The length field of a byte count `hi:lo`: `count >> 61`, whose high half
is zero, then `8 count`. -/
theorem lenOf_halves (h l : BitVec 32) :
    Proof.Sha512.md.lenOf (h ++ l) = Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (h >>> 29) ++
      bytes64 true (BitVec.ofNat 64 (8 * (h ++ l).toNat)) := by
  rw [Proof.Sha512.lenOf_split, wordBytes_split, hi_shr61, lo_shr61, Proof.Sha512.Arm.hi_append]
  rfl

/-- The length field, at `r0 + 176`: zero, `count >> 61` (from its high half
in `r5`), then `8 count` (`len64`). -/
theorem len_ok (s : State) (hfit : (s.gpr .r0).toNat + (64 + 128) ≤ 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 (64 + (128 - 16))) 16) :
    WP isa (.block params.len) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (64 + (128 - 16)))
        (Proof.Sha512.md.lenOf (s.gpr .r5 ++ s.gpr .r4)) := by
  have a176 : State.addr (s.gpr .r0 + BitVec.ofNat 32 176) = State.addr (s.gpr .r0) + BitVec.ofNat 64 176 :=
    addr_off (by omega)
  have a180 : State.addr (s.gpr .r0 + BitVec.ofNat 32 180) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 176 + BitVec.ofNat 64 4 := by
    rw [addr_off (by omega), add_ofNat]
  have o176 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 176) 4 := by
    simpa using InRegions.offset hout (off := 0) (m := 4) (by omega) (by omega)
  have o180 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 176 + BitVec.ofNat 64 4) 4 :=
    InRegions.offset hout (by omega) (by omega)
  have o184 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 184) 8 := by
    have := InRegions.offset hout (off := 8) (m := 8) (by omega) (by omega)
    rwa [add_ofNat] at this
  show WP isa (.block (.mov .r9 (.imm 0) :: .str .r9 .r0 176 :: .mov .r9 (.shifted .r5 .lsr 29) ::
    .rev .r9 .r9 :: .str .r9 .r0 180 :: len64 184 true)) s _
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_str (by decide)
    (by rw [u₁.other _ (by decide), a176]) (by rw [u₁.wr]; exact o176) fun s₂ g₂ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_rev fun s₄ u₄ => wp_str (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), a180])
    (by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr]; exact o180) fun s₅ g₅ => ?_
  have k₅ : ∀ r, r ≠ .r9 → s₅.gpr r = s.gpr r := fun r h => by
    rw [g₅.gpr, u₄.other r h, u₃.other r h, g₂.gpr, u₁.other r h]
  refine (len64_ok (d := 184) (be := true) (by decide) (by rw [k₅ _ (by decide)]; omega)
    (by rw [g₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, k₅ _ (by decide)]; exact o184)).mono
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r h => by rw [g r h, k₅ r h], by rw [rd, g₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd],
      by rw [wr, g₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr], by rw [sp, g₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp], ?_⟩
  have v₄ : s₄.gpr .r9 = rev (s.gpr .r5 >>> 29) := by
    rw [u₄.gpr, u₃.gpr, g₂.gpr, u₁.other _ (by decide)]
  have v₁ : s₁.gpr .r9 = rev 0 := by rw [u₁.gpr]; decide
  have e184 : State.addr (s.gpr .r0) + BitVec.ofNat 64 184 = State.addr (s.gpr .r0) + BitVec.ofNat 64 176 +
      BitVec.ofNat 64 (Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (s.gpr .r5 >>> 29)).length := by
    rw [add_ofNat]; rfl
  have e176 : State.addr (s.gpr .r0) + BitVec.ofNat 64 (64 + (128 - 16)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 176 := rfl
  rw [m, k₅ _ (by decide), k₅ _ (by decide), k₅ _ (by decide), g₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, v₄,
    v₁, writeW_rev, writeW_rev, show (4 : Nat) = (Spec.Sha256.wordBytes 0).length from rfl,
    writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), e184,
    writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes, bytes64_length]), lenOf_halves, e176]

/-! ## The digest -/

/-- The first `n` words of the final hash value at `p0` (`r0`), big-endian, to `p6` (`r6`). -/
theorem out_ok {p0 p6 : BitVec 32} (f0 : p0.toNat + 64 ≤ 2 ^ 32) (f6 : p6.toNat + 64 ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p0, 64⟩ ⟨State.addr p6, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r0 = p0 → s.gpr .r6 = p6 →
    InRegions (s.rd ++ s.wr) (State.addr p0) 64 → InRegions s.wr (State.addr p6) 64 →
    (∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p6) (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap outW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h0 h6 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h0 h6 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hP := flat_length (stateAt s.mem (State.addr p0)) n (by omega)
    simp only [outW, List.cons_append, List.nil_append]
    have i₀ : ∀ o, o + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 4 :=
      fun o ho => by
        rw [rd₁, wr₁]; exact InRegions.offset hin (by omega) (by omega)
    have o₀ : ∀ o, o + 4 ≤ 8 → InRegions s₁.wr (State.addr p6 + BitVec.ofNat 64 (8 * n + o)) 4 :=
      fun o ho => by rw [wr₁]; exact InRegions.offset hout (by omega) (by omega)
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [g₁ _ (by decide) (by decide), h0, addr_add (by omega)]; rfl) (i₀ 0 (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h0, addr_add (by omega)])
      (by rw [u₂.rd, u₂.wr]; exact i₀ 4 (by omega)) fun s₃ u₃ => wp_rev fun s₄ u₄ => wp_rev fun s₅ u₅ => ?_
    have e6 : s₅.gpr .r6 = p6 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h6]
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [e6, addr_add (by omega)]; rfl) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 0 (by omega))
      fun s₆ g₆ => ?_
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [g₆.gpr, e6, addr_add (by omega)]) (by rw [g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 4 (by omega))
      fun s₇ g₇ => k s₇ (fun r h9 h10 => by
          rw [g₇.gpr, g₆.gpr, u₅.other r h9, u₄.other r h10, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁])
        (by rw [g₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    -- The word's halves, as in `s`: the writes so far are to `p6`.
    have hread : ∀ o, o + 4 ≤ 8 → s₁.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 =
        s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 := by
      intro o ho
      rw [m₁]
      refine (writeBytes_frame s.mem (State.addr p6) _ (R := ⟨State.addr p6, 64⟩) ?_).readW
        (r := ⟨State.addr p0 + BitVec.ofNat 64 (8 * n + o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hP]; simpa using Offset.contains_base (State.addr p6) (d := 0) (n := 8 * n) (k := 64) (by omega)
          (by decide)
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega))
    have hw : (stateAt s.mem (State.addr p0))[n] = s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n)) 64 := by
      simp [stateAt]
    have wlo : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) 32 =
        lo (stateAt s.mem (State.addr p0))[n] := by
      rw [hw, readW_lo, Nat.add_zero]
    have whi : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) 32 =
        hi (stateAt s.mem (State.addr p0))[n] := by
      rw [hw, readW_hi, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have v10 : s₅.gpr .r10 = rev (hi (stateAt s.mem (State.addr p0))[n]) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.mem, hread 4 (by omega), whi]
    have v9 : s₆.gpr .r9 = rev (lo (stateAt s.mem (State.addr p0))[n]) := by
      rw [g₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hread 0 (by omega), wlo]
    have a4 : State.addr p6 + BitVec.ofNat 64 (8 * n + 4) =
        State.addr p6 + BitVec.ofNat 64 (8 * n + 0) +
          BitVec.ofNat 64 (Spec.Sha256.wordBytes (hi (stateAt s.mem (State.addr p0))[n])).length := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    have a8 : State.addr p6 + BitVec.ofNat 64 (8 * n + 0) = State.addr p6 +
        BitVec.ofNat 64 (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes).length := by
      rw [hP]; rfl
    rw [g₇.mem, v9, g₆.mem, v10, u₅.mem, u₄.mem, u₃.mem, u₂.mem, writeW_rev, writeW_rev, a4,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), ← wordBytes_split, m₁, a8,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem shape : Shape (P := params) Proof.Sha512.md where
  len s hfit hout := len_ok s hfit hout
  out s f₀ f₆ hin hout hd := by
    rw [← List.append_nil params.out]
    refine out_ok f₀ f₆ hd 8 (Nat.le_refl _) [] s _ rfl rfl hin hout fun s' g rd wr sp m => WP.block_nil
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, List.take_of_length_le (by simp)]
    rfl

theorem finalize_verified : Verified Arm.target Impl.Sha512.Arm.Stream.finalize Proof.Sha512.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_sha512_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc => h iv m hr hl hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

end VG.Proof.Sha512.Arm.Stream.Finalize
