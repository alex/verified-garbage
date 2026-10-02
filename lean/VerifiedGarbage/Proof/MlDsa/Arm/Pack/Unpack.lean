import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y`, plus `q` if that is negative
(`bm`), which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`. The loop
is proven once for every width (`unpackLoop_ok`); `unpackLoop_buFin_ok` states
what the loop of `buFin B` does for any state, which `vg_mldsa_bit_unpack` (by
its five cases, in its frame) and ExpandMask use.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_frame)
open VG.Proof.MlDsa.Pack

/-! ## The coefficients -/

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := bm (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok {B : Nat} (hB : encodable (BitVec.ofNat 32 B) = true) (d : Nat) : FinOk (buFin B) d (buWord B) :=
  fun j s hj hout _ => by
    refine WP.keep _ ?_ rfl
    unfold buFin bMinus addQNeg
    run_block [hj, hout, hB, buWord, bm, BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := BitVec.ofNat 32 y <<< 13

theorem t1Fin_ok : FinOk t1Fin 10 t1Word := fun j s hj hout _ => by
  refine WP.keep _ ?_ rfl
  unfold t1Fin
  run_block [hj, hout, t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## The loop of `BitUnpack`, for any state

`unpackLoop (buFin B) d c nb` for `BitUnpack(v, a, B)` with `bitlen (a + B) = d`
(ExpandMask runs it for `(B, d, c, nb)` = `(2¹⁷, 18, 4, 9)` and
`(2¹⁹, 20, 2, 5)`, with `a = B - 1`), from any state in which `r0` holds
the address of `32 d` readable bytes and `r1` that of a writable
polynomial, disjoint and not wrapping around: it writes `BitUnpack` of the
bytes to the polynomial, reduced, and changes nothing else but the
registers `r0`–`r4` and `r12` (`unpackRegs`) and the flags. Its constant
time (with `r0` and `r1` public) is `unpackLoop_ct18` and `unpackLoop_ct20`.
-/

theorem unpackLoop_buFin_ok {B d c nb : Nat} (hs : Shape d c nb) (hB : encodable (BitVec.ofNat 32 B) = true)
    (hB19 : B ≤ 2 ^ 19) {a : Nat} (hd : bitlen (a + B) = d) {s : State}
    (hin : (⟨State.addr (s.gpr .r0), 32 * d⟩ : Region) ∈ s.rd ++ s.wr)
    (hout : polyRegion (State.addr (s.gpr .r1)) ∈ s.wr)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), 32 * d⟩ (polyRegion (State.addr (s.gpr .r1))))
    (fitV : (s.gpr .r0).toNat + 32 * d ≤ 2 ^ 32) (fitP : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32) :
    WP isa (unpackLoop (buFin B) d c nb) s fun s' =>
      PolyIs s'.mem (State.addr (s.gpr .r1)) (toRq (bitUnpack (bytesAt s.mem (State.addr (s.gpr .r0)) (32 * d)) a B)) ∧
        Frame [polyRegion (State.addr (s.gpr .r1))] s.mem s'.mem ∧ Keep unpackRegs s s' := by
  refine WP.mono (unpackLoop_ok (buFin_ok hB d) hs hin hout hsep fitV fitP rfl rfl rfl rfl rfl)
    fun s' ⟨hc, hf, hk⟩ => ⟨?_, hf, hk⟩
  have hq := q_eq
  refine polyIs_of_toNat fun i hi => ?_
  have hy := field_lt (inNum s.mem (State.addr (s.gpr .r0)) d) d i hs.d20
  have hy' := hy
  unfold inNum at hy'
  rw [hc i hi, buWord, bm_toNat (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi, hd,
    ofInt_sub (by omega)]

/-- The loop of `BitUnpack` is constant time, with `r0` and `r1` public. -/
theorem unpackLoop_ct18 {P : State → State → Prop} (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1) :
    RelCT isa P (unpackLoop (buFin 131072) 18 4 9) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r0, .r1]) (fun a b h => Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(hP a b h).1, (hP a b h).2]) (by taint_decide)

theorem unpackLoop_ct20 {P : State → State → Prop} (hP : ∀ a b, P a b → a.gpr .r0 = b.gpr .r0 ∧ a.gpr .r1 = b.gpr .r1) :
    RelCT isa P (unpackLoop (buFin 524288) 20 2 5) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r0, .r1]) (fun a b h => Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [(hP a b h).1, (hP a b h).2]) (by taint_decide)

/-! ## `vg_mldsa_bit_unpack` -/

theorem ldrSp_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa (.block [.ldrSp .r12 0]) s fun s' =>
      (s'.gpr .r12 = stackArg s 0 ∧ s'.mem = s.mem) ∧ Keep [.r12] s s' := by
  have h' : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 := h
  refine WP.keep _ ?_ rfl
  run_block [h', and_true]
  rfl

theorem buPro_ok (s : State) :
    WP isa (.block [.mov .r1 (.reg .r12)]) s fun s' => (s'.gpr .r1 = s.gpr .r12 ∧ s'.mem = s.mem) ∧ Keep [.r1] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

/-- What `bitUnpack` leaves. -/
def BuPost (s₀ s' : State) : Prop :=
  PolyIs s'.mem (State.addr (stackArg s₀ 0))
    (toRq (bitUnpack (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (s₀.gpr .r2).toNat
      (s₀.gpr .r3).toNat)) ∧ abiPreserved s₀ s'

theorem bu_wp {s₀ : State} (hp : BuPre s₀) : WP isa Impl.MlDsa.Arm.Pack.bitUnpack s₀ (BuPost s₀) := by
  unfold Impl.MlDsa.Arm.Pack.bitUnpack
  refine WP.seq (WP.mono (ldrSp_ok s₀ ⟨_, by rw [hp.rd]; simp, Region.contains_self _ _⟩)
    fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ => ?_)
  have sp₁ : s₁.sp = s₀.sp := k₁.2.2.2
  have hsp : 4 ≤ s₁.sp.toNat := by rw [sp₁]; exact hp.sp4
  have eb : below4 s₁ = below4 s₀ := by rw [below4, below4, sp₁]
  refine WP.frame (rs := [.r4]) (r := .r4) rfl (by simpa using hsp) (by decide) ?_
  refine WP.seq (WP.mono (buPro_ok _) fun s₂ ⟨⟨g₂, m₂⟩, k₂⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have g0 : ∀ r, r ≠ .r12 → r ≠ .r1 → s₂.gpr r = s₀.gpr r := fun r h12 h1 => by
    rw [k₂.gpr (by simp [h1]), pushed_gpr, k₁.gpr (by simp [h12])]
  have go : ∀ {d c nb B : Nat}, Shape d c nb → (s₀.gpr .r3).toNat = B → B ≤ 2 ^ 19 →
      encodable (BitVec.ofNat 32 B) = true → bitlen ((s₀.gpr .r2).toNat + B) = d → ∀ s : State, Same s₂ s →
      WP isa (unpackLoop (buFin B) d c nb) s fun s₃ => BuPost s₀ (popped .r4 4 s₃) := by
    intro d c nb B hs hB hB19 hBe hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have x0 : s.gpr .r0 = s₀.gpr .r0 := by rw [hS.1, g0 _ (by decide) (by decide)]
    have x1 : s.gpr .r1 = stackArg s₀ 0 := by rw [hS.1, g₂, pushed_gpr, g₁]
    have xrd : s.rd = s₀.rd := by rw [hS.2.2.1, k₂.2.1, pushed_rd, k₁.2.1]
    have xwr : s.wr = ⟨State.addr (s₁.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)), 4 * [Reg.r4].length⟩ :: s₀.wr := by
      rw [hS.2.2.2.1, k₂.2.2.1, pushed_wr, k₁.2.2.1]
    have xm : s.mem = (pushed [.r4] s₁).mem := by rw [hS.2.1, m₂]
    refine WP.mono (unpackLoop_buFin_ok (s := s) hs hBe hB19 hd
      (by rw [x0, xrd, hp.rd, ← hlen]; exact List.mem_append_left _ (List.mem_cons_self ..))
      (by rw [x1, xwr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (by rw [x0, x1, ← hlen]; exact hp.disj) (by rw [x0, ← hlen]; exact hp.fitV) (by rw [x1]; exact hp.fitP))
      fun s₃ ⟨hpoly, hf, hk⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
    · rw [popped_mem, ← x1, hlen]
      rw [x0, xm, bytesAt_frame (pushed4_frame hsp) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [eb, ← hlen]; exact hp.bV.symm) (by omega), m₁,
        ← hB] at hpoly
      exact hpoly
    · -- The registers: `r4` from the frame, the others kept.
      have hsp₃ : s₃.sp = s₁.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₂.2.2.2, pushed4_sp]
      by_cases h4 : r = .r4
      · subst h4
        rw [(popped4 hsp hsp₃ ?_).1, k₁.gpr (by decide)]
        rw [hf.readW (r := below4 s₁) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [x1, eb]; exact hp.bP) (by decide),
          xm, pushed4_mem hsp, Mem.readW_writeW_self32]
      · have hr' : r ∉ unpackRegs := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h4 | decide
        have h12 : r ≠ .r12 := fun e => hr' (by rw [e]; decide)
        have h1 : r ≠ .r1 := fun e => hr' (by rw [e]; decide)
        rw [popped_gpr h4, hk.gpr hr', hS.1, g0 r h12 h1]
    · have hsp₃ : s₃.sp = s₁.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₂.2.2.2, pushed4_sp]
      rw [popped_sp, hsp₃, ← sp₁]; exact BitVec.sub_add_cancel _ _
  have e3 : ∀ s, Same s₂ s → (s.gpr .r3).toNat = (s₀.gpr .r3).toNat := fun s h => by
    rw [h.1, g0 _ (by decide) (by decide)]
  refine sel_ok .r3 2 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n2 => ?_)
  · rw [e3 s₂ ⟨rfl, rfl, rfl, rfl, rfl⟩] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 2 by omega]; decide) s₃ h₃
  rw [e3 s₂ ⟨rfl, rfl, rfl, rfl, rfl⟩] at n2
  refine sel_ok .r3 4 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4 => ?_)
  · rw [e3 s₃ h₃] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 4 by omega]; decide) s₄ (h₃.trans h₄)
  rw [e3 s₃ h₃] at n4
  refine sel_ok .r3 4096 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n4096 => ?_)
  · rw [e3 s₄ (h₃.trans h₄)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 4095 by omega]; decide) s₅ ((h₃.trans h₄).trans h₅)
  rw [e3 s₄ (h₃.trans h₄)] at n4096
  refine sel_ok .r3 131072 (by decide) (by decide) _ _ s₅ (fun s₆ h₆ e => ?_) (fun s₆ h₆ n17 => ?_)
  · rw [e3 s₅ ((h₃.trans h₄).trans h₅)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 131071 by omega]; decide) s₆ (((h₃.trans h₄).trans h₅).trans h₆)
  · rw [e3 s₅ ((h₃.trans h₄).trans h₅)] at n17
    have e : (s₀.gpr .r3).toNat = 524288 := by omega
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 524287 by omega]; decide) s₆ (((h₃.trans h₄).trans h₅).trans h₆)

theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

theorem bitUnpack_ct :
    ConstantTime isa (bitUnpackContract Arm.abi 4).pre (bitUnpackContract Arm.abi 4).pub
      Impl.MlDsa.Arm.Pack.bitUnpack := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp₁ hp₂ hpub e₁ e₂
  have q₁ := BuPre.of hp₁
  have q₂ := BuPre.of hp₂
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
  obtain ⟨hsp, h0, h1, h2, h3, harg⟩ := hpub
  have A := (relct_ldrSp (t := .r12) (off := 0) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)).wp
    (F₁ := fun (a : State) => (a.gpr .r12 = stackArg s₁ 0 ∧ a.mem = s₁.mem) ∧ Keep [.r12] s₁ a)
    (F₂ := fun (a : State) => (a.gpr .r12 = stackArg s₂ 0 ∧ a.mem = s₂.mem) ∧ Keep [.r12] s₂ a)
    fun a b h => by
      rw [h.1, h.2]
      exact ⟨ldrSp_ok s₁ ⟨_, by rw [q₁.rd]; simp, Region.contains_self _ _⟩,
        ldrSp_ok s₂ ⟨_, by rw [q₂.rd]; simp, Region.contains_self _ _⟩⟩
  have B := frame4_ct (body := bitUnpackBody) [.r0, .r1, .r2, .r3, .r12] (by taint_decide)
    (P := fun a b => True ∧ ((a.gpr .r12 = stackArg s₁ 0 ∧ a.mem = s₁.mem) ∧ Keep [.r12] s₁ a) ∧
      ((b.gpr .r12 = stackArg s₂ 0 ∧ b.mem = s₂.mem) ∧ Keep [.r12] s₂ b))
    (fun a b ⟨_, ⟨_, ka⟩, ⟨_, kb⟩⟩ => by rw [ka.2.2.2, kb.2.2.2]; exact hsp)
    (fun a b ⟨_, ⟨⟨a12, _⟩, ka⟩, ⟨⟨b12, _⟩, kb⟩⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h0
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h1
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h2
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h3
      · rw [a12, b12]; exact harg)
  exact ((A.seq B) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition: `f` = `0x2000` on the stack. -/
def buSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 96 | .r2 => 2 | .r3 => 2 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x20 else 0
  rd := [⟨0x1000, 96⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, bitUnpackContract Arm.abi 4 =
    bitUnpackApi.sig.contract Arm.target.abi pre post bitUnpackApi.writeArgs 4 leak := ⟨_, _, _, rfl⟩

theorem bitUnpack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.bitUnpack (bitUnpackContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, bitUnpack_ct, ?_⟩
  · obtain ⟨t, s', he, hb, habi⟩ := bu_wp (BuPre.of hs)
    refine ⟨t, s', he, habi, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hb
  · refine ⟨buSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | decide +kernel

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : T1Pre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.unpackT1 s₀ fun s' =>
      PolyIs s'.mem (State.addr (s₀.gpr .r1))
        ((simpleBitUnpack (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) ∧
        Keep unpackRegs s₀ s' := by
  refine WP.mono (unpackLoop_ok t1Fin_ok (c := 4) (nb := 5) (by constructor <;> decide) (pv := s₀.gpr .r0)
    (pp := s₀.gpr .r1) (m₀ := s₀.mem) (rd := s₀.rd) (wr := s₀.wr)
    (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hp.wr]; exact List.mem_singleton_self _) hp.disj hp.fitV hp.fitP rfl rfl rfl rfl rfl)
    fun s' ⟨hc, _, hk⟩ => ⟨?_, hk⟩
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (State.addr (s₀.gpr .r0)) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, t1Word, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), Vector.getElem_map,
    simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

/-- `unpackT1` writes no register the ABI preserves. -/
theorem t1_preserves : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.MlDsa.Arm.Pack.unpackT1, dstOf i ≠ some r := by
  have h : (instrs Impl.MlDsa.Arm.Pack.unpackT1).all
      (fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- A state satisfying the precondition. -/
def t1Sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, unpackT1Contract Arm.abi =
    unpackT1Api.sig.contract Arm.target.abi pre post unpackT1Api.writeArgs 0 leak := ⟨_, _, _, rfl⟩

theorem unpackT1_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.unpackT1 (unpackT1Contract Arm.abi) := by
  refine ⟨fun s hs => ?_, Proof.MlKem.Arm.Add.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpost, hk⟩ := t1_wp (T1Pre.of hs)
    refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (t1_preserves r hr) he, hk.2.2.2⟩, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hpost
  · sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨t1Sat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals decide +kernel

end VG.Proof.MlDsa.Arm.Pack
