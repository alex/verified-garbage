import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.Points

/-! Compact point tables in the caller's eight-KiB workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem Ctx.ptr_nat {b : BitVec 32} {s : State} (hc : Ctx b s) {o : Nat} (ho : o < 8192) :
    (b + BitVec.ofNat 32 o).toNat = b.toNat + o := by
  have hb := hc.fit
  rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]

theorem Ctx.ptr_addr {b : BitVec 32} {s : State} (hc : Ctx b s) {o : Nat} (ho : o < 8192) :
    State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o :=
  addr_add (by have := hc.fit; omega)

structure TableKeep (b : BitVec 32) (o n : Nat) (s t : State) : Prop where
  rest : Rest [.r2, .r3] s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem

theorem TableKeep.ctx {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (hc : Ctx b s) : Ctx b t := hc.of_rest h.rest (by decide)

theorem TableKeep.trans {b : BitVec 32} {s t u : State} {o n : Nat}
    (h : TableKeep b o n s t) (k : TableKeep b o n t u) : TableKeep b o n s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem TableKeep.mono {b : BitVec 32} {s t : State} {o n o' n' : Nat}
    (h : TableKeep b o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableKeep b o' n' s t :=
  ⟨h.rest, h.frame.sub fun r hm => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩

theorem TableKeep.slot {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (hn : o + n ≤ 8192) (i : Slot)
    (hsep : offset i + 64 ≤ o ∨ o + n ≤ offset i) :
    ∀ k < 16, limb t.mem (State.addr b) (offset i) k = limb s.mem (State.addr b) (offset i) k := by
  have hi := slot_range i
  rw [ACC_eq] at hi
  refine limb_frame h.frame fun r hm k hk => ?_
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem TableKeep.env {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192) : env t.mem b = env s.mem b := by
  funext i
  have hi := slot_range i
  rw [ACC_eq] at hi
  exact congrArg VG.Proof.X25519.toFe (val16_congr (h.slot hn i (.inl (by omega))))

theorem TableKeep.lim {b : BitVec 32} {s t : State} {o n : Nat}
    (h : TableKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192)
    (hl : AllLim s.mem b) : AllLim t.mem b := by
  intro i k hk
  have hi := slot_range i
  rw [ACC_eq] at hi
  rw [h.slot hn i (.inl (by omega)) k hk]
  exact hl i k hk

def tableF (m : Mem) (b : BitVec 32) (o : Nat) : Spec.X25519.Fe :=
  packedF m (State.addr b + BitVec.ofNat 64 o)

theorem TableKeep.tableF {b : BitVec 32} {s t : State} {o n d : Nat}
    (h : TableKeep b o n s t) (hn : o + n ≤ 8192) (hd : d + 32 ≤ 8192)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : tableF t.mem b d = tableF s.mem b d := by
  refine congrArg VG.Proof.X25519.toFe (packedV_frame h.frame fun r hm => ?_)
  rw [List.mem_singleton.mp hm]
  exact Offset.disjoint _ hsep (by omega) (by omega)

theorem toTableQuarter_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (packField (64 + 64 * j) (32 * j))) s fun t =>
      tableF t.mem b (o + 32 * j) = env s.mem b ⟨j, by omega⟩ ∧
      TableKeep b (o + 32 * j) 32 s t := by
  have ea := hc.ptr_addr (by omega : o < 8192)
  refine WP.mono (packField_ok hc (by omega) (hl ⟨j, by omega⟩) (by omega) hp
    (by rw [hc.ptr_nat (by omega)]; have := hc.fit; omega)
    (fun i hi => by rw [ea, Offset.add_add]; exact in_base hc.wr (by omega) (by omega))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)))
    fun t ⟨hr, hf, hv⟩ => ?_
  rw [ea, Offset.add_add] at hf hv
  exact ⟨congrArg VG.Proof.X25519.toFe hv, ⟨hr.mono (by decide), hf⟩⟩

theorem toTablePrefix_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => packField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), tableF t.mem b (o + 32 * j) = env s.mem b ⟨j, by omega⟩) ∧
      TableKeep b o (32 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (toTableQuarter_ok (hk.ctx hc) (hk.lim hlo (by omega) hl)
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · rw [ku.tableF (by omega) (by omega) (.inl (by omega)), hv j h]
    · have e : j = n := by omega
      subst j
      rw [hu, hk.env hlo (by omega)]

def tablePoint (m : Mem) (b : BitVec 32) (o : Nat) : Spec.Ed25519.Point :=
  ⟨tableF m b o, tableF m b (o + 32), tableF m b (o + 64), tableF m b (o + 96)⟩

theorem pointToTable_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t => tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 ∧
      TableKeep b o 128 s t := by
  refine WP.mono (toTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hk⟩
  simp only [tablePoint, point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.Arm
