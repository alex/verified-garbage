import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Words
import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize

/-!
# The SHA-512 family's digest on ARMv7

The streaming `finalize`'s code writing the final hash value
(`Impl.Sha512.Arm.Stream.outW`, each 64-bit word big-endian, from its halves
stored low first) writes the digest of `Proof.Sha512.md` (`OutOk`), as HMAC
and PBKDF2 use it.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Sha512.Arm.Stream (outW)
open VG.Proof.MdStream.Arm (wp_ldr wp_str wp_rev)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open VG.Proof.Sha512.Arm.Stream.Finalize (wordBytes_split writeW_rev flat_length)
open VG.Proof.Sha512.Arm (readW_lo readW_hi)
open VG.Spec.Sha512 (HashValue stateAt wordBytes)

/-- The first `n` words of the final hash value at `p0` (`r0`), big-endian, to `p6` (`r6`). -/
theorem out64_ok {p0 p6 : BitVec 32} (f0 : p0.toNat + 64 ≤ 2 ^ 32) (f6 : p6.toNat + 64 ≤ 2 ^ 32)
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
        rw [rd₁, wr₁]; exact MdStream.Arm.InRegions.offset hin (by omega) (by omega)
    have o₀ : ∀ o, o + 4 ≤ 8 → InRegions s₁.wr (State.addr p6 + BitVec.ofNat 64 (8 * n + o)) 4 :=
      fun o ho => by rw [wr₁]; exact MdStream.Arm.InRegions.offset hout (by omega) (by omega)
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [g₁ _ (by decide) (by decide), h0, addr_add (by omega)]; rfl) (i₀ 0 (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h0, addr_add (by omega)])
      (by rw [u₂.rd, u₂.wr]; exact i₀ 4 (by omega)) fun s₃ u₃ => wp_rev fun s₄ u₄ => wp_rev fun s₅ u₅ => ?_
    have e6 : s₅.gpr .r6 = p6 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h6]
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [e6, addr_add (by omega)]; rfl) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 0 (by omega)) fun s₆ g₆ => ?_
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [g₆.gpr, e6, addr_add (by omega)]) (by rw [g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 4 (by omega))
      fun s₇ g₇ => k s₇ (fun r h9 h10 => by
          rw [g₇.gpr, g₆.gpr, u₅.other r h9, u₄.other r h10, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    -- The word's halves, as in `s`: the writes so far are to `p6`.
    have hread : ∀ o, o + 4 ≤ 8 → s₁.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 =
        s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 := by
      intro o ho
      rw [m₁]
      refine (writeBytes_frame s.mem (State.addr p6) _ (R := ⟨State.addr p6, 64⟩) ?_).readW
        (r := ⟨State.addr p0 + BitVec.ofNat 64 (8 * n + o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hP]; exact Memory.contains_base (by omega)
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega))
    have hw : (stateAt s.mem (State.addr p0))[n] = s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n)) 64 := by
      simp [stateAt]
    have wlo : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) 32 = lo (stateAt s.mem (State.addr p0))[n] := by
      rw [hw, readW_lo, Nat.add_zero]
    have whi : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) 32 = hi (stateAt s.mem (State.addr p0))[n] := by
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

/-- The SHA-512 family's digest code, as HMAC and PBKDF2 use it. -/
theorem sha512_out : OutOk Proof.Sha512.md ((List.range 8).flatMap outW) := by
  intro s f₀ f₆ hin hout hd
  rw [← List.append_nil ((List.range 8).flatMap outW)]
  refine out64_ok f₀ f₆ hd 8 (Nat.le_refl _) [] s _ rfl rfl hin hout fun s' g rd wr sp m => WP.block_nil
    ⟨g, rd, wr, sp, ?_⟩
  rw [m, List.take_of_length_le (by simp)]
  rfl

end VG.Proof.Pbkdf2.Md.Arm
