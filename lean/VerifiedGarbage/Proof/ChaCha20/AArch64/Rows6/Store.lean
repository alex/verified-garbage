import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (xor_write_apply)

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 24, s'.v (vreg k) = s.v (vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : StoreSame s₀ s₁) (h' : StoreSame s₁ s₂) :
    StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem xorRow_ok (s : State) (k : Fin 24)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (xorRow k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 ^^^ s.v (vreg k)) ∧ StoreSame s u := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    obtain ⟨q,hq,hc⟩ := hout; exact ⟨q,List.mem_append_right _ hq,hc⟩
  have ha : 16 * k.val % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [xorRow,runBlock_cons,runBlock_nil,exec,addr,ha,and_self,ite_true,State.load,hin,
    Option.bind_some,Option.map_some,isa,runStep_some,RegUpd.gpr_setV,RegUpd.v_setV,
    vreg_ne,ite_false,VOp.eval,State.store,RegUpd.wr_setV,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl⟩
  intro l
  simp only [RegUpd.v_setV,vreg_ne,ite_false]

/-- A sequence of distinct, aligned vector stores, tracked by their 16-byte slot. -/
def Data (m₀ m : Mem) (p : Addr) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < 384
    then m₀ x ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem Data.nil (m : Mem) (p : Addr) (out : Nat → BitVec 128) : Data m m p out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem Data.store {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) {n : Nat} (hn : n < 24) (hfresh : n ∉ done) :
    Data m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (p + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) p out (n :: done) := by
  intro x
  rw [xor_write_apply]
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  rw [h x]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < 384
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [hd, and_self, ite_true, he, hfresh, false_and, ite_false, hs,
      List.mem_cons_self, hb]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd]
    by_cases hb : (x - p).toNat < 384
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

theorem xorList_ok (ks : List (Fin 24)) (hn : ks.Nodup)
    {m₀ : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : Data m₀ s.mem p out done) (hp : s.gpr .x1 = p)
    (hv : ∀ k : Fin 24, s.v (vreg k) = out k.val)
    (hfresh : ∀ k ∈ ks, k.val ∉ done)
    (hout : ∀ k ∈ ks, InRegions s.wr (p + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (ks.flatMap xorRow)) s fun u =>
      Data m₀ u.mem p out (ks.map Fin.val ++ done) ∧ StoreSame s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨hd,rfl,fun _ => rfl,rfl,rfl,rfl⟩
  | cons k ks ih =>
    have ho : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hp]; exact hout k (List.mem_cons_self ..)
    apply WP.block_append
    refine (xorRow_ok s k ho).mono fun a ⟨hm,hs⟩ => ?_
    have hd' : Data m₀ a.mem p out (k.val :: done) := by
      rw [hm,hp,hv k]; exact hd.store k.isLt (hfresh k (List.mem_cons_self ..))
    have hp' : a.gpr .x1 = p := by rw [hs.gpr,hp]
    have hv' : ∀ l : Fin 24, a.v (vreg l) = out l.val := by intro l; rw [hs.v,hv]
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 ((Fin.ext e) ▸ hl),
        hfresh l (List.mem_cons_of_mem _ hl)⟩
    have ho' : ∀ l ∈ ks, InRegions a.wr (p + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l hl; rw [hs.wr]; exact hout l (List.mem_cons_of_mem _ hl)
    refine (ih (List.nodup_cons.mp hn).2 hd' hp' hv' hf' ho').mono fun u ⟨hu,hau⟩ => ⟨?_,hs.trans hau⟩
    intro x
    simpa only [Data,List.map_cons,List.cons_append,List.mem_append,List.mem_cons,or_assoc,
      or_left_comm] using hu x
end VG.Proof.ChaCha20.AArch64.Rows6
