import VerifiedGarbage.Proof.Ed25519.Arm.Mul
import VerifiedGarbage.Proof.Ed25519.Arm.Cswap

/-!
# Ed25519 on ARMv7: the field elements the working space holds

Untrusted: everything here is checked by Lean. `SlotsOk m B qs v`: each slot
`q` of `qs` holds limbs below `2¹⁶` of the element `v q`. The field
operations as updates of `v` (`mulS`, `addS`, `subS`, `cswapS`), for slots
whose separation from the output is decided on their offsets (`Sep1`), and
writing only the field area `[64, 1600)` of the working space (`FA`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm
open VG.Proof.X25519.Arm
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds limbs below `2¹⁶` of `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, Lim m B q ∧ FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => ⟨(h q hq).1, (h q hq).2.trans (hs q hq)⟩

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

/-- Every slot of `qs` is `o` or separate from it, and in `[64, ACC)`. -/
def Sep1 (o : Nat) (qs : List Nat) : Bool :=
  qs.all fun q => (q == o || q + 64 ≤ o || o + 64 ≤ q) && 64 ≤ q && q + 64 ≤ ACC

theorem sep1_get {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 64 ≤ o ∨ o + 64 ≤ q) ∧ 64 ≤ q ∧ q + 64 ≤ ACC := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[64, 1600)` of the working space: the elements and `ACC`. -/
abbrev FA (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, 1536⟩

section
variable {b : BitVec 32}

/-- The slots of `qs` other than `o` after a write of `o` (and `ACC`). -/
theorem slots_after {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true) (ho : o + 64 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m (State.addr b) qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    Lim m' (State.addr b) q ∧ FS m' (State.addr b) q = v q := by
  obtain ⟨h1, h2, h3⟩ := sep1_get hq hq'
  have hA := ACC_eq
  have e : ∀ k < 16, limb m' (State.addr b) q k = limb m (State.addr b) q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, ?_⟩
  rw [FS, V, val16_congr e]; exact (hS q hq').2

theorem frame_FA {o : Nat} (ho : 64 ≤ o ∧ o + 64 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m') :
    Frame [FA b] m m' := by
  have hA := ACC_eq
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)

theorem mulS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (mul o x y) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x * v y)) := by
  refine WP.mono (mul_ok ho.2 (sep1_get hq hx).2.2 (sep1_get hq hy).2.2 hc (hS x hx).1 (hS y hy).1)
    fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho.2 hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem addS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x + v y)) := by
  have hA := ACC_eq
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (add_ok (by omega) (by omega) (by omega)
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_add hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho.2 (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) (o :: qs) (upd v o (v x - v y)) := by
  have hA := ACC_eq
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (sub_ok (by omega) (by omega) (by omega)
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_sub hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho.2 (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

theorem cswapS {x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 x qs = true) (hq' : Sep1 y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x) {s : State} (hc : Ctx b s) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s.gpr .r9 = 0 - BitVec.ofNat 32 sw) (hS : SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.r2, .r3, .r4] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr b) qs (swapV x y sw v) := by
  have hA := ACC_eq
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  refine WP.mono (cswap_ok (b := b) (by omega) (by omega) hxy hc hsw h9) fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)
  · intro q hq''
    have hlx : ∀ k < 16, limb s'.mem (State.addr b) x k =
        sel sw (limb s.mem (State.addr b) x k) (limb s.mem (State.addr b) y k) := h.lx
    have hly : ∀ k < 16, limb s'.mem (State.addr b) y k =
        sel sw (limb s.mem (State.addr b) y k) (limb s.mem (State.addr b) x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hx).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS q hx).2
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) y k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS y hy).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS y hy).2
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hy).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS q hy).2
      · have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) x k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS x hx).1 k hk, ?_⟩
        rw [FS, V, val16_congr e]; exact (hS x hx).2
    · simp only [swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h2, h3⟩ := sep1_get hq hq''
      obtain ⟨h1', -, -⟩ := sep1_get hq' hq''
      have e : ∀ k < 16, limb s'.mem (State.addr b) q k = limb s.mem (State.addr b) q k :=
        limb_frame h.frame fun r hr k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq'').1 k hk, ?_⟩
      rw [FS, V, val16_congr e]; exact (hS q hq'').2

end

end VG.Proof.Ed25519.Arm
