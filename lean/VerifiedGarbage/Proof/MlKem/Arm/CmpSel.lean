import VerifiedGarbage.Proof.MlKem.Arm.Prf

/-!
# ML-KEM-768 on 32-bit ARM: comparing `c` with `c'`, and selecting the key

Untrusted: everything here is checked by Lean. `compare` ORs the XORs of the
bytes of two buffers into `r12` (`compare_ok`: 0 exactly when they are
equal); `selSetup` turns it into a mask, all ones exactly when it is 0
(`selSetup_ok`); and the loop of `selBody` writes, byte by byte, the first
source under the mask and the second one otherwise (`select_ok`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## `compare` -/

section
variable {s : State} {x y c a : BitVec 32}

theorem cmpBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h9 : s.gpr .r9 = c) (h12 : s.gpr .r12 = a)
    (ir0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ir1 : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block cmpBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r9 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r12 = a ||| ((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 ^^^
        (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r := by
  run_block [cmpBody, h0, h1, h9, h12, ir0, ir1, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After comparing `k` bytes of `S` and `D`. -/
structure CmpInv (S D : BitVec 32) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = S + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (1 * k)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (1 * (len - k))
  cs : ∀ r ∈ preserved, r ≠ .r9 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lt : (s.gpr .r12).toNat < 256
  eq : s.gpr .r12 = 0 ↔ ∀ t < k, s₀.mem (State.addr S + BitVec.ofNat 64 t) = s₀.mem (State.addr D + BitVec.ofNat 64 t)

theorem setWidth32_inj {a b : Byte} (h : a.setWidth 32 = b.setWidth 32) : a = b := by
  have := congrArg (BitVec.setWidth 8) h
  rwa [setWidth_byte, setWidth_byte] at this

theorem cmp_step {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32)
    (cr : Covers [⟨State.addr S, len⟩, ⟨State.addr D, len⟩] (s₀.rd ++ s₀.wr))
    {k : Nat} (hk : k < len) {s : State} (h : CmpInv S D len s₀ k s) :
    WP isa (.block cmpBody) s fun s' => CmpInv S D len s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = len) := by
  have eS : State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr S + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eD : State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cS : (⟨State.addr S, len⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cD : (⟨State.addr D, len⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (cmpBody_ok h.r0 h.r1 h.r9 rfl
    (by rw [eS, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cS⟩)
    (by rw [eD, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cD⟩))
    fun s' ⟨r0, r1, r9, z, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr h9 => (cs r hr h9).trans (h.cs r hr h9),
      m.trans h.mem, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r9]; exact count_sub (k := 1) hk
  · rw [r12, BitVec.toNat_or, BitVec.toNat_xor]
    have ha := h.lt
    have hx := (s.mem (State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0))).isLt
    have hy := (s.mem (State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0))).isLt
    rw [setWidth32_toNat, setWidth32_toNat]
    exact Nat.or_lt_two_pow (n := 8) ha (Nat.xor_lt_two_pow (n := 8) hx hy)
  · rw [r12, eS, eD, h.mem]
    constructor
    · intro h₀ t ht
      obtain ⟨h₁, h₂⟩ := BitVec.or_eq_zero_iff.mp h₀
      by_cases e : t = k
      · subst e; exact setWidth32_inj (BitVec.xor_eq_zero_iff.mp h₂)
      · exact h.eq.mp h₁ t (by omega)
    · intro h₁
      exact BitVec.or_eq_zero_iff.mpr ⟨h.eq.mpr fun t ht => h₁ t (by omega),
        BitVec.xor_eq_zero_iff.mpr (congrArg _ (h₁ k (by omega)))⟩
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

theorem cmpArgs_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C) :
    WP isa (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 oCt, .mov .r12 (.imm 0), .mov .r9 (.imm 1088)]) s
      fun s' => s'.gpr .r0 = C ∧ s'.gpr .r1 = P + BitVec.ofNat 32 oCt ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r9 = BitVec.ofNat 32 1088 ∧ (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e1 : encodable (BitVec.ofNat 32 oCt) = true := by decide
  have e2 : encodable (0 : BitVec 32) = true := by decide
  have e3 : encodable (1088 : BitVec 32) = true := by decide
  run_block [ptrTo, e1, e2, e3, h7, h6, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- `compare`: `r12` is 0 exactly when the 1088 bytes at `C` (in `r6`) and at
`P + 19456` (`r7 = P`) are equal. -/
theorem compare_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C)
    (fC : C.toNat + 1088 ≤ 2 ^ 32) (fD : (P + BitVec.ofNat 32 oCt).toNat + 1088 ≤ 2 ^ 32)
    (cr : Covers [⟨State.addr C, 1088⟩, ⟨State.addr (P + BitVec.ofNat 32 oCt), 1088⟩] (s.rd ++ s.wr)) :
    WP isa compare s fun s' => (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (s'.gpr .r12).toNat < 256 ∧
      (s'.gpr .r12 = 0 ↔ bytesAt s.mem (State.addr C) 1088 = bytesAt s.mem (State.addr (P + BitVec.ofNat 32 oCt)) 1088) := by
  refine WP.seq (WP.mono (cmpArgs_ok h7 h6) fun s₁ ⟨g0, g1, g12, g9, cs, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (CmpInv C (P + BitVec.ofNat 32 oCt) 1088 s₁) (N := 1088) (by decide)
    (fun k hk s h => cmp_step fC fD (by decide) (by rw [rd, wr]; exact cr) hk h)
    (fun s' h => ⟨fun r hr h9 => (h.cs r hr h9).trans (cs r hr h9), h.mem.trans m, h.rd.trans rd, h.wr.trans wr,
      h.sp.trans sp, h.lt, ?_⟩)
    ⟨by rw [g0]; simp, by rw [g1]; simp, by rw [g9], fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  rw [h.eq, ← m]
  constructor
  · intro he
    exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [he t ht, bytesAt_getElem]
  · intro he t ht
    have := congrArg (fun L : List Byte => L[t]!) he
    simp only [bytesAt_getElem! _ _ ht] at this
    exact this

/-! ## The mask -/

theorem mask_eq : ∀ n < 256, (0 : BitVec 32) - (BitVec.ofNat 32 n - 1) >>> 31 =
    if n = 0 then BitVec.allOnes 32 else 0 := by
  decide +kernel

theorem mask_of {v : BitVec 32} (h : v.toNat < 256) :
    (0 : BitVec 32) - (v - 1) >>> 31 = if v = 0 then BitVec.allOnes 32 else 0 := by
  have := mask_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem selSetup_ok {s : State} {P K : BitVec 32} (h7 : s.gpr .r7 = P) (hlt : (s.gpr .r12).toNat < 256)
    (hk : s.mem.readW (State.addr (P + BitVec.ofNat 32 oExtra)) 32 = K)
    (ik : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 oExtra)) 4) :
    WP isa (.block selSetup) s fun s' =>
      s'.gpr .r12 = (if s.gpr .r12 = 0 then BitVec.allOnes 32 else 0) ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oG ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 oKbar ∧ s'.gpr .r2 = K ∧ s'.gpr .r9 = BitVec.ofNat 32 32 ∧
      (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e1 : encodable (1 : BitVec 32) = true := by decide
  have e0 : encodable (0 : BitVec 32) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 oG) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oKbar) = true := by decide
  have e4 : encodable (32 : BitVec 32) = true := by decide
  have o1 : oExtra < 4096 := by decide
  run_block [selSetup, ptrTo, e1, e0, e2, e3, e4, o1, h7, ik, hk, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]
  exact mask_of hlt

/-! ## `select` -/

section
variable {s : State} {x y z c m : BitVec 32}

theorem selBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = z) (h9 : s.gpr .r9 = c)
    (h12 : s.gpr .r12 = m)
    (ir0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ir1 : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1)
    (iw : InRegions s.wr (State.addr (z + BitVec.ofNat 32 0)) 1) :
    WP isa (.block selBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r2 = z + 1 ∧ s'.gpr .r9 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r12 = m ∧
      s'.mem = s.mem.writeW (State.addr (z + BitVec.ofNat 32 0))
        (((((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32 ^^^
            (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32) &&& m) ^^^
          (s.mem (State.addr (y + BitVec.ofNat 32 0))).setWidth 32).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r := by
  run_block [selBody, h0, h1, h2, h9, h12, ir0, ir1, iw, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

theorem sel_byte (a b : Byte) (e : Bool) :
    ((((a.setWidth 32 ^^^ b.setWidth 32) &&& (if e then BitVec.allOnes 32 else 0)) ^^^ b.setWidth 32).setWidth 8) =
      if e then a else b := by
  cases e
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, setWidth_byte]

/-- After selecting `k` bytes of `X` or `Y` into `Z`. -/
structure SelInv (X Y Z : BitVec 32) (e : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = X + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = Y + BitVec.ofNat 32 (1 * k)
  r2 : s.gpr .r2 = Z + BitVec.ofNat 32 (1 * k)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (1 * (32 - k))
  r12 : s.gpr .r12 = if e then BitVec.allOnes 32 else 0
  cs : ∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr Z, 32⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (State.addr Z + BitVec.ofNat 64 t) =
    if e then s₀.mem (State.addr X + BitVec.ofNat 64 t) else s₀.mem (State.addr Y + BitVec.ofNat 64 t)

theorem sel_step {X Y Z : BitVec 32} {e : Bool} {s₀ : State} (fX : X.toNat + 32 ≤ 2 ^ 32)
    (fY : Y.toNat + 32 ≤ 2 ^ 32) (fZ : Z.toNat + 32 ≤ 2 ^ 32)
    (dX : (⟨State.addr X, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (dY : (⟨State.addr Y, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (cr : Covers [⟨State.addr X, 32⟩, ⟨State.addr Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr Z, 32⟩] s₀.wr)
    {k : Nat} (hk : k < 32) {s : State} (h : SelInv X Y Z e s₀ k s) :
    WP isa (.block selBody) s fun s' => SelInv X Y Z e s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 32) := by
  have eX : State.addr (X + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr X + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eY : State.addr (Y + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr Y + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eZ : State.addr (Z + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr Z + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cX : (⟨State.addr X, 32⟩ : Region).Contains (State.addr X + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cY : (⟨State.addr Y, 32⟩ : Region).Contains (State.addr Y + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cZ : (⟨State.addr Z, 32⟩ : Region).Contains (State.addr Z + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (selBody_ok h.r0 h.r1 h.r2 h.r9 h.r12
    (by rw [eX, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cX⟩)
    (by rw [eY, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cY⟩)
    (by rw [eZ, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cZ⟩))
    fun s' ⟨r0, r1, r2, r9, z, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, ?_, r12,
      fun r hr h9 h10 => (cs r hr h9 h10).trans (h.cs r hr h9 h10), rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
      ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r2]; exact ptr_succ _ 1 k
  · rw [r9]; exact count_sub (k := 1) hk
  · rw [m, eZ]; exact h.frame.writeW (List.mem_singleton_self _) _ cZ
  · have hX : s.mem (State.addr X + BitVec.ofNat 64 k) = s₀.mem (State.addr X + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dX _ cX
    have hY : s.mem (State.addr Y + BitVec.ofNat 64 k) = s₀.mem (State.addr Y + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dY _ cY
    rw [m, eZ, eX, eY, byte_writeW8 _ _ (by omega) (by omega), sel_byte, hX, hY]
    by_cases et : t = k
    · subst et; rw [ite_eq_left rfl]
    · rw [ite_eq_right et]; exact h.bytes t (by omega)
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

/-- The loop of `selBody`: the 32 bytes at `X` if `e`, and at `Y` otherwise, into `Z`. -/
theorem select_ok {X Y Z : BitVec 32} {e : Bool} {s₀ : State} (fX : X.toNat + 32 ≤ 2 ^ 32)
    (fY : Y.toNat + 32 ≤ 2 ^ 32) (fZ : Z.toNat + 32 ≤ 2 ^ 32)
    (dX : (⟨State.addr X, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (dY : (⟨State.addr Y, 32⟩ : Region).Disjoint ⟨State.addr Z, 32⟩)
    (cr : Covers [⟨State.addr X, 32⟩, ⟨State.addr Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr Z, 32⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = X) (h1 : s₀.gpr .r1 = Y) (h2 : s₀.gpr .r2 = Z) (h9 : s₀.gpr .r9 = BitVec.ofNat 32 32)
    (h12 : s₀.gpr .r12 = if e then BitVec.allOnes 32 else 0) :
    WP isa (.loop (.block selBody) .ne) s₀ fun s =>
      (∀ r ∈ preserved, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨State.addr Z, 32⟩] s₀.mem s.mem ∧
      bytesAt s.mem (State.addr Z) 32 = if e then bytesAt s₀.mem (State.addr X) 32 else bytesAt s₀.mem (State.addr Y) 32 :=
  wp_loop_ne (SelInv X Y Z e s₀) (N := 32) (by decide) (fun k hk s h => sel_step fX fY fZ dX dY cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, by
      cases e
      · show bytesAt s.mem (State.addr Z) 32 = bytesAt s₀.mem (State.addr Y) 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [h.bytes t ht, bytesAt_getElem]; rfl
      · show bytesAt s.mem (State.addr Z) 32 = bytesAt s₀.mem (State.addr X) 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [h.bytes t ht, bytesAt_getElem]; rfl⟩)
    ⟨by rw [h0]; simp, by rw [h1]; simp, by rw [h2]; simp, by rw [h9], h12, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

end VG.Proof.MlKem.Arm
